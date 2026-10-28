# Mathematical attribution and code provenance

**Samuel Kittle and Constantin Kogler** are the authors of the two primary
mathematical works and their results. References are listed in
[BIBLIOGRAPHY.md](BIBLIOGRAPHY.md). Constantin Kogler is the responsible
formalization maintainer and copyright holder of the authored repository material.

The Lean implementation was generated with OpenAI Codex assistance, including
adaptation, compilation and automated semantic review. This records how the
code was produced; mathematical authorship remains with the named human authors.
No independent human review of the formalization is asserted.

The contained development adapts the earlier 0BSD LpSelfSimilar proof library
and its BernoulliCubic extension. The source repositories were
`lp-densities-lean` at commit `1ede5c88a2f7fcbb43907447f2363db89fbde0a2`
and `bernoulli-exponent-three-lean` at commit
`bfdcb9fc506387335c964c6dde6693d09237476e`. The cumulative development supplies
both mathematical proof routes without duplicate namespace definitions.
The [reuse manifest](reused-source.json) records source correspondence and exact
hashes, distinguishing the module visibility transform from further adaptations
and new modules. It is a source record, not a verification receipt. These are
contained source copies; neither predecessor checkout is a build dependency.

Adaptations include the current Lean module system and public declaration
visibility, compatibility changes for the pinned Mathlib release, the revised
quantitative reverse Hölder statement, explicit Section 3 interfaces, and the
non-strict exponent-100 endpoint. [SOURCE_NOTES.md](SOURCE_NOTES.md) explains
mathematical proof variants separately from implementation changes.

Original and adapted code and documentation retain the BSD Zero Clause license
in [LICENSE](../LICENSE). Lean, Mathlib and verification tools keep their own
licenses. Citing a mathematical work does not relicense it under the software
license. Bibliographic authorship is distinct from software copyright and
formalization maintenance.
