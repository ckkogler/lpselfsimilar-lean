# Verification evidence

The complete default build and all-authored axiom audit passed on 28 October
2026. All five independent introduction claims passed strict comparison and
kernel replay with Lean, NanoDa and con-ron. A fresh isolated checkout rebuilt
the library and reproduced the same audit with sibling proof projects hidden.

The [self-similar measures paper (PDF)](http://constantinkogler.com/Files/L1LpSelfSimilar.pdf)
and the [coverage map](../COVERAGE.md) provide the source statements and their
corresponding Lean declarations.

| Record | Scope |
| --- | --- |
| [Library checks](library-checks.json) | Default Lake build: 4,745 jobs; 774 authored module artifacts; all 3,603 authored declarations audited. |
| [Strict comparison](comparison-checks.json) | Five introduction claims and their ordinary definition dependency closure; Lean, NanoDa and con-ron accepted. The con-ron replay checked 74,355 exported declarations. |
| [Independent Challenge](challenge-provenance.json) | Challenge compiled separately using the pinned Lean and clean Mathlib dependency closure. There are no definition holes. |
| [Isolated reproduction](relocation-checks.json) | Fresh Git clone, no authored artifacts initially, read-only pinned dependency caches, network isolation and hidden sibling proofs; identical 3,603-declaration audit. |
| [Semantic review](semantic-review.json) | Introduction statements, revised supporting results, source coverage and migration, with the scope and limits of agent review. |
| [Policy review](policy-review.json) | Exact official policy revision, supported toolchain, kernel selection and source requirements. |
| [Repository checks](repository-checks.json) | Official metadata, source, dependency, Challenge-limit and license checks. |

The [proof snapshot](proof-source-snapshot.json) binds the build and axiom audit
to the exact authored sources and build configuration. The
[comparison snapshot](comparison-source-snapshot.json) additionally binds the
Challenge, comparison configuration, checking scripts and CI workflow. The
checked candidate commit is recorded in the receipts. Later documentation and
receipt additions are outside those snapshots; final metadata and repository
checks are recorded separately. No receipt is a self-referential hash of the
final repository.

The five deliberate theorem holes in Challenge are outside the proved Solution
closure. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
The environment-based audit includes definitions, instances and generated
auxiliaries. Mathematical statement review is distinct from kernel checking.

The receipts summarize actual commands, process exits, tool versions and output
hashes. Raw logs and exports are retained outside the public source tree.
Local checks do not establish hosted CI success, Palomar registration or
acceptance, or independent human peer review.
