#!/usr/bin/env python3
"""Strict local comparison using the pinned Palomar policy and checker versions.

Challenge is compiled separately against canonical dependencies. The comparison
judges retained exports with Lean and NanoDa; the policy-selected con-ron then
replays the same Solution export in a read-only sandbox. No registry API is used.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import socket
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PIPELINE_COMMIT = "a93fc88c092faeef1a92b1c905e688aab8e80795"
TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
LEAN_REVISION = "11acb17ec6b07a8f9e9173e6845197929540936b"


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            digest.update(chunk)
    return digest.hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def output(argv: list[str], **kwargs) -> str:
    return subprocess.check_output(argv, text=True, **kwargs).strip()


def source_snapshot() -> dict[str, str]:
    snapshot = {}
    for directory, directories, files in os.walk(ROOT, followlinks=False):
        directories[:] = sorted(d for d in directories if d not in {".git", ".lake"})
        for name in directories:
            require(not (Path(directory) / name).is_symlink(),
                    f"Unexpected public directory symlink: {Path(directory) / name}")
        for name in sorted(files):
            path = Path(directory) / name
            require(not path.is_symlink(), f"Unexpected public symlink: {path}")
            snapshot[path.relative_to(ROOT).as_posix()] = sha256(path)
    return snapshot


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pipeline", type=Path, default=ROOT / ".lake/palomar-pipeline")
    parser.add_argument("--prepare-only", action="store_true")
    parser.add_argument("--kernel-cache", type=Path, default=ROOT / ".lake/palomar-checker")
    args = parser.parse_args()
    pipeline = args.pipeline.resolve()
    require(output(["git", "-C", str(pipeline), "rev-parse", "HEAD"]) == PIPELINE_COMMIT,
            "The official policy checkout has the wrong revision.")
    subprocess.run(["git", "-C", str(pipeline), "diff", "--exit-code", "HEAD"], check=True)
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(pipeline))
    from scripts import checker_updates, kernel_outcomes, verify_submission as official

    environment = os.environ.copy()
    for name in ["ELAN_TOOLCHAIN", "LEAN_PATH", "LEAN_SRC_PATH", "LAKE_PACKAGES_DIR",
                 "LAKE_HOME", "LEAN", "LEAN_SYSROOT", "LAKE_OVERRIDE_LEAN"]:
        environment.pop(name, None)
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN, "Unexpected toolchain.")
    official.supported_toolchain(TOOLCHAIN)
    prefix = Path(output(["lean", "--print-prefix"], cwd=ROOT, env=environment)).resolve()
    version = output([str(prefix / "bin/lean"), "--version"])
    require("4.35.0-rc2" in version and LEAN_REVISION in version, "Unexpected Lean binary revision.")
    binaries = official.toolchain_tools(prefix)
    environment["PATH"] = str(prefix / "bin") + os.pathsep + environment.get("PATH", "")
    bwrap_value = shutil.which(environment.get("COMPARATOR_BWRAP", "bwrap"), path=environment["PATH"])
    require(bwrap_value is not None, "Install bubblewrap 0.12.0 or set COMPARATOR_BWRAP.")
    bwrap = Path(bwrap_value).resolve()
    require(output([str(bwrap), "--version"]) == "bubblewrap 0.12.0", "Wrong bubblewrap revision.")
    environment["COMPARATOR_BWRAP"] = str(bwrap)

    kernel_cache = args.kernel_cache.resolve()
    revision = checker_updates.selected_revision(TOOLCHAIN)
    require(revision is not None, "Expected a maintainer-pinned con-ron update for this toolchain.")
    checker = kernel_cache / "con-ron"
    if checker.exists():
        require(sha256(checker) == revision["binary_sha256"], "Cached con-ron digest differs.")
        checker_record = {"kind": "maintainer-pinned-release", "source_toolchain": TOOLCHAIN, **revision}
    else:
        require(not kernel_cache.exists(), "Incomplete checker cache; use a new --kernel-cache path.")
        checker, checker_record = checker_updates.materialize_checker(
            TOOLCHAIN, binaries["con-ron"], kernel_cache)

    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    run = ROOT / ".lake/verification" / ("comparison-" + stamp)
    run.mkdir(parents=True)
    receipt = {"status": "running", "started_utc": stamp, "policy_commit": PIPELINE_COMMIT,
               "verifier_sha256": sha256(Path(__file__)),
               "execution": {"host": socket.getfqdn(),
                             "slurm_job_id": os.environ.get("SLURM_JOB_ID"),
                             "cpu_affinity": sorted(os.sched_getaffinity(0))},
               "source_hashes": source_snapshot(), "lean_version": version,
               "tool_sha256": {**{name: sha256(path) for name, path in binaries.items()},
                                "bubblewrap": sha256(bwrap), "selected_con_ron": sha256(checker)},
               "selected_con_ron": checker_record, "commands": [],
               "scope": "Local strict comparison and kernel replay; not the hosted registry pipeline."}
    receipt_path = run / "receipt.json"

    def save():
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n")

    def execute(label: str, argv: list[str], *, cwd=ROOT, env=None, destination=None,
                check=True, timeout=None):
        started = datetime.now(timezone.utc).isoformat()
        stdout_path = destination or (run / (label + ".stdout"))
        stderr_path = run / (label + ".stderr")
        timed_out = False
        with stdout_path.open("wb") as out, stderr_path.open("wb") as err:
            try:
                result = subprocess.run(argv, cwd=cwd, env=env or environment,
                                        stdout=out, stderr=err, timeout=timeout)
                returncode = result.returncode
            except subprocess.TimeoutExpired:
                timed_out = True
                returncode = None
        record = {"label": label, "command": argv, "started_utc": started,
                  "finished_utc": datetime.now(timezone.utc).isoformat(), "exit_code": returncode,
                  "timed_out": timed_out, "timeout_seconds": timeout,
                  "stdout": stdout_path.name, "stderr": stderr_path.name,
                  "stdout_sha256": sha256(stdout_path), "stderr_sha256": sha256(stderr_path)}
        receipt["commands"].append(record)
        save()
        print(f"{label}: {'timeout' if timed_out else 'exit ' + str(returncode)}", flush=True)
        if check and (timed_out or returncode):
            print(stderr_path.read_text(errors="replace")[-12000:], file=sys.stderr)
            raise RuntimeError(f"{label} failed: see {run}")
        return returncode, stdout_path, stderr_path

    save()
    try:
        config = official.load_comparator_config(ROOT / "comparator.json")
        require(set(config["permitted_axioms"]) == official.STANDARD_AXIOMS, "Unexpected axiom set.")
        config.pop("enable_nanoda", None)
        config["external_kernels"] = {"nanoda": [str(binaries["nanoda_bin"])]}
        protected = run / "comparator.json"
        protected.write_text(json.dumps(config, indent=2) + "\n")
        protected_digest = sha256(protected)
        packages = official.manifest_packages(ROOT)
        package_roots = []
        for package in packages:
            require(not package["url"].startswith("path:"), "Unexpected path dependency.")
            directory = ROOT / ".lake/packages" / package["name"]
            require(output(["git", "-C", str(directory), "rev-parse", "HEAD"]) == package["revision"],
                    "Dependency checkout mismatch: " + package["name"])
            subprocess.run(["git", "-C", str(directory), "diff", "--exit-code", "HEAD"], check=True)
            require(not output(["git", "-C", str(directory), "ls-files", "--others", "--exclude-standard"]),
                    "Dependency contains nonignored untracked files: " + package["name"])
            package_roots.append(directory.resolve())
        canonical_packages = official.manifest_packages(ROOT / ".lake/packages/mathlib")
        require({item["name"] for item in packages} == {item["name"] for item in canonical_packages} | {"mathlib"},
                "Challenge trust is restricted to Mathlib and its exact manifest closure.")
        official.trusted_package_url_map(packages, canonical_packages)
        official.check_mathlib_toolchain(ROOT, packages, checkout=ROOT,
                                        project_toolchain=TOOLCHAIN, project_toolchain_path="lean-toolchain")
        if args.prepare_only:
            receipt["status"] = "prepared"
            receipt["scope"] = "Tool and dependency preparation only; comparison has not run."
            save()
            print(receipt_path, flush=True)
            return 0

        canonical = run / "canonical"
        canonical.mkdir()
        challenge = canonical / "Challenge.lean"
        shutil.copyfile(ROOT / "Challenge.lean", challenge)
        trusted_env = environment.copy()
        trusted_env["LEAN_PATH"] = os.pathsep.join(
            [str(prefix / "lib/lean")] + [str(path / ".lake/build/lib/lean") for path in package_roots])
        trusted_env["LEAN_SRC_PATH"] = os.pathsep.join(
            [str(canonical), str(prefix / "src/lean"), str(prefix / "src/lean/lake")] +
            [str(path) for path in package_roots])
        execute("challenge-build", [str(binaries["lean"]), "-o", str(canonical / "Challenge.olean"),
                                    str(challenge)], cwd=canonical, env=trusted_env)
        _, dep_file, _ = execute("challenge-imports", [str(binaries["lean"]), "--src-deps", str(challenge)],
                                 cwd=canonical, env=trusted_env)
        source_dependencies = [Path(line).resolve() for line in dep_file.read_text().splitlines() if line.strip()]
        trusted_roots = [prefix, *package_roots]
        require(all(any(path.is_relative_to(base) for base in trusted_roots) for path in source_dependencies),
                "Challenge imports a source outside canonical dependencies.")
        receipt["challenge_imports"] = {str(path): sha256(path) for path in source_dependencies}
        targets = official.comparator_export_targets(config, official.primitive_targets(prefix))
        receipt["export_targets"] = targets
        trusted_env["LEAN_PATH"] = str(canonical) + os.pathsep + trusted_env["LEAN_PATH"]
        challenge_export = run / "challenge.export"
        execute("challenge-export", [str(binaries["leanexport"]), "Challenge", "--", *targets],
                cwd=canonical, env=trusted_env, destination=challenge_export)
        official.verify_export(challenge_export)
        challenge_digest = sha256(challenge_export)

        execute("solution-build", [str(binaries["lake"]), "build", "Solution"])
        solution_export = run / "solution.export"
        execute("solution-export", [str(binaries["lake"]), "env", str(binaries["leanexport"]),
                                    "Solution", "--", *targets], destination=solution_export)
        official.verify_export(solution_export)
        solution_digest = sha256(solution_export)
        require(sha256(challenge_export) == challenge_digest,
                "The canonical Challenge export changed during the Solution phase.")
        require(sha256(protected) == protected_digest,
                "The protected comparison configuration changed.")
        judge = run / "judge"
        judge.mkdir()
        execute("comparator", [str(binaries["lake"]), "comparator", "--config", str(protected),
                               "--challenge-from-export", str(challenge_export),
                               "--solution-from-export", str(solution_export)], cwd=judge)
        # Give the supplemental checker only its authenticated executable,
        # runtime libraries and the exact export already accepted above.
        replay = [str(bwrap), "--unshare-all", "--die-with-parent", "--new-session",
                  "--proc", "/proc", "--dev", "/dev", "--tmpfs", "/tmp"]
        for path in [Path("/usr"), Path("/bin"), Path("/lib"), Path("/lib64"), prefix]:
            if path.exists():
                replay += ["--ro-bind", str(path), str(path)]
        replay += ["--ro-bind", str(checker), "/checker", "--ro-bind", str(solution_export),
                   "/solution.export", "--chdir", "/tmp", "--", "/checker", "--jobs=2",
                   "--verified", "/solution.export"]
        rc, out, err = execute("con-ron", replay, cwd=judge, check=False,
                               timeout=official.CON_RON_REPLAY_SECONDS)
        if rc is None:
            outcome = {"name": "con-ron", "status": "declined", "reason": "capacity",
                       "exit_code": None, "detail": "The official replay time budget expired.",
                       "budget_seconds": official.CON_RON_REPLAY_SECONDS}
        else:
            outcome = kernel_outcomes.con_ron_outcome(rc, out.read_text(errors="replace"),
                                                    err.read_text(errors="replace"))
        receipt["con_ron_outcome"] = outcome
        require(outcome["status"] in {"accepted", "declined"}, "con-ron rejected or failed unexpectedly.")
        require(sha256(challenge_export) == challenge_digest and
                sha256(solution_export) == solution_digest and sha256(protected) == protected_digest,
                "A retained export or comparison configuration changed during judgment.")
        require(receipt["source_hashes"] == source_snapshot(), "Public sources changed during verification.")
        receipt["status"] = "pass"
        receipt["kernels"] = ["Lean default", "NanoDa"] + (["con-ron"] if outcome["status"] == "accepted" else [])
        receipt["exports"] = {"challenge_sha256": challenge_digest,
                              "solution_sha256": solution_digest,
                              "protected_config_sha256": protected_digest}
        return 0
    except Exception as error:
        receipt["status"] = "fail"
        receipt["error"] = str(error)
        raise
    finally:
        receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
        print(receipt_path, flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
