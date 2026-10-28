# Lp densities of self-similar measures and Bernoulli convolutions

This repository formalizes the results of Samuel Kittle and Constantin Kogler
on higher integrability of self-similar measures and explicit continuous
densities for Bernoulli convolutions. It combines
[*On Lp density of self similar measures and Bernoulli convolutions* (PDF)](L1LpSelfSimilar.pdf)
with *A cubic criterion for continuous
algebraic Bernoulli convolutions*.

An absolutely continuous self-similar measure on Euclidean space has a density
in Lp for some p > 1. For an algebraic parameter lambda in (1/2,1), put

    B = (1 + degree(lambda) + log(Mahler(lambda))) / min(1, log(Mahler(lambda))).

The condition `lambda >= 1 - B^(-3)` gives an L2 density at lambda squared and
a continuous compactly supported density at lambda. The exponent-100 criterion
is also retained, including its endpoint. For reduced rational parameters
`lambda = 1-p/q`, the condition is `p <= q/(2+log q)^3`; in particular every
integer `n >= 588` gives a continuous density at `1-1/n`.

[Challenge.lean](Challenge.lean) gives independent definitions and the five
introduction claims. [Solution.lean](Solution.lean) imports their complete
proof library. Supporting results, including the quantitative reverse Hölder
criterion, Gaussian detail estimates and the cubic working criterion, belong
to the library and its comprehensive audit.

- [COVERAGE.md](COVERAGE.md): source results and their Lean declarations.
- [FORMALIZATION.md](FORMALIZATION.md): definitions, proof structure and fidelity.
- [provenance](provenance/README.md): mathematical sources and contained code reuse.
- [verification](verification/README.md): exact checked snapshots and outcomes.
- [formalization.yaml](formalization.yaml) and [comparator.json](comparator.json):
  submission metadata and the statement comparison configuration.

The complete library builds, and its 3,603 authored declarations pass the axiom
audit. All five introduction claims pass strict comparison and replay with Lean,
NanoDa and con-ron. A fresh isolated checkout rebuilds the library and reproduces
the same audit. The [verification records](verification/README.md) identify the
checked sources, tools and scope.

## Build and audit

The project pins **Lean v4.35.0-rc2** and **Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`**, with every dependency revision
committed in [lake-manifest.json](lake-manifest.json). From the repository root:

```sh
lake exe cache get
lake build
lake env lean Verification.lean
```

The cache command is optional. The default build includes the full authored
library and Solution. Verification prints every authored declaration's type
and audits its transitive axioms, including definitions, instances and generated
auxiliaries. Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
The deliberate Challenge holes remain outside the proved import closure.

All proof sources are contained here. Building requires no sibling project,
private source document or local path outside the repository and its pinned tools.

## Reproduce local Palomar checks

The checking scripts use the official [PalomarSubmission policy](https://github.com/PalomarRegistry/PalomarSubmission)
at commit `a93fc88c092faeef1a92b1c905e688aab8e80795`. They run local checks and
make no submission request. Before a later submission, recheck current policy.

Use Linux, Python 3.11, Ruby 3.3.12, Bundler 2.7.2 and the pinned Lean toolchain:

```sh
git clone https://github.com/PalomarRegistry/PalomarSubmission.git .lake/palomar-pipeline
git -C .lake/palomar-pipeline checkout --detach a93fc88c092faeef1a92b1c905e688aab8e80795
python3 -m venv .lake/palomar-python
.lake/palomar-python/bin/python -m pip install --require-hashes --no-deps -r .lake/palomar-pipeline/requirements.txt
export BUNDLE_GEMFILE="$PWD/.lake/palomar-pipeline/Gemfile"
export BUNDLE_PATH="$PWD/.lake/palomar-gems"
export BUNDLE_FROZEN=true
bundle install
.lake/palomar-python/bin/python scripts/validate_local_contract.py
```

Strict comparison uses bubblewrap 0.12.0 and the authenticated kernel versions
selected by that policy. Its installer may require host package installation:

```sh
export COMPARATOR_BWRAP="$(.lake/palomar-pipeline/scripts/install_bwrap.sh "$PWD/.lake/palomar-bwrap")"
.lake/palomar-python/bin/python scripts/verify_palomar.py
```

The checker records the exact executable hashes and source snapshot. The
[CI workflow](.github/workflows/verify.yml) follows the same build, audit,
contract-validation and comparison sequence. A workflow definition does not
establish that a hosted run has passed.

## Attribution and license

The mathematical results are due to **Samuel Kittle and Constantin Kogler**.
Constantin Kogler is the responsible formalization maintainer. The Lean code was
generated with OpenAI Codex assistance and checked with the recorded tools;
this is distinct from authorship of the mathematics. Original and adapted code
and documentation use [0BSD](LICENSE), with reuse recorded in
[provenance](provenance/README.md).
