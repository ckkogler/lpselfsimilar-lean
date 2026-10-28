# Mathematical definitions and proof structure

The primary mathematical sources are the two papers of Samuel Kittle and
Constantin Kogler listed in [provenance/BIBLIOGRAPHY.md](provenance/BIBLIOGRAPHY.md).
[COVERAGE.md](COVERAGE.md) maps their results to the contained Lean development.

## The statement boundary

The five claims in [Challenge.lean](Challenge.lean) are the self-similar higher
integrability theorem, the non-strict exponent-100 algebraic criterion, the
cubic criterion with both density conclusions, the rational cubic criterion,
and its consequence for every integer denominator at least 588. Identical
claims appearing in both introductions are stated once. All five are selected
by Comparator. Supporting lemmas and historical variants remain in the library.

Challenge imports Mathlib only. Its ordinary definitions have no holes;
only the five theorem proofs are placeholders. Solution imports the proved
library and excludes Challenge. Matching theorem names alone are insufficient:
Comparator checks their types and the definitions used by those types.

Euclidean space is Mathlib's `EuclideanSpace`. A similarity consists of a
positive metric scale, a real linear isometry and a translation. Reflections
are allowed through the isometry. A finite system uses nonnegative weights
summing to one, and stationarity is an actual weighted pushforward equation.
Neither separation nor a common contraction ratio is assumed. Compact support
is derived from stationarity and contraction rather than supplied as an extra
hypothesis of the higher-integrability theorem.

The Bernoulli convolution is the pushforward of the countable product measure
of fair Boolean digits under the infinite sign series. Convergence, independence,
stationarity, support and decomposition into residue classes are proved in the
library. It is not an abstract measure stipulated to have a density.

Algebraic degree is the degree of the rational minimal polynomial. Clearing its
denominators, removing content and normalizing its sign gives the canonical
primitive integer minimal polynomial. Mahler measure is Mathlib's polynomial
Mahler measure of this integer polynomial, with the root-product identity proved
in the library. All logarithms in the public criteria are natural logarithms.

Each density conclusion is an equality with Lebesgue measure weighted by an
everywhere nonnegative real function. Lp assertions use Mathlib's `MemLp`.
The continuous-density conclusions include compact support. The cubic theorem
retains the L2 density at the squared parameter as a separate conjunct, rather
than merely asserting continuity at the original parameter.

## Higher integrability and the exponent-100 criterion

Self-similarity bounds the mass of small sets inside balls. Finite stopping-word
partitions provide the required averaged pushforward identity, including zero
weights and degenerate supports. A quantitative weak reverse Hölder argument
then gives higher integrability.

The revised weak reverse Hölder lemma uses `C=18^d` and the exact exponent
`1+log(1/(C*eta))/log(C/epsilon)`. The earlier `21^d` lemma is preserved under its
original public interface. Its weaker exponent is not substituted for the
revised statement.

The final reverse Hölder theorem uses dyadic stopping radii and an eightfold
enlargement. A separate six-adic stopping argument with a triple covering proves
the source's exact level recurrence (2.2), including coefficient `2*6^d*eta`
and summation ratio `2*(1/3)^d`. Both constructions use discrete stopping radii
in place of the source's maximal-radius selection.

The Bernoulli argument passes from arithmetic separation and entropy to block
conditional variance, then Gaussian detail decay and a bounded approximation
to the density. The resulting quantitative Lp gain, selection of a power of the
parameter and Young's convolution inequality yield continuity. The exponent-100
endpoint follows from the proved gap condition `(1-lambda)*B^100<2`:
the source's non-strict hypothesis gives a bound of at most one.

The revised floor choice `k=floor(20-20 log(1-lambda))` and its exponential
cost estimate are retained explicitly. A monotonicity argument reduces the
numerical bound to an exact rational certificate at the endpoint `t=400`.

The scaled-convolution lemma treats arbitrary positive scales and compactly
supported densities with `p >= k/(k-1)`, including `p=infinity`. The
bounded-approximation lemma applies
to the supplied density, and the higher-to-first detail estimate includes its
order-one endpoint. Details of proof variants and source corrections are recorded
in [provenance/SOURCE_NOTES.md](provenance/SOURCE_NOTES.md).

## The cubic criterion

The cubic proof strengthens the entropy input to exact constants independent
of the algebraic degree in the entropy factor. Canonical Gaussian channels and
contracting-conjugate matrices give the required comparison; conditional
expectation, conditional variance and information identities are proved for
those actual probability laws.

Finite graph entropy localizes uncertainty among distinct merged digit sums.
Distance-band decompositions and independent digit packing produce Fourier
cancellation. Quintic cutoff estimates, justified derivatives and integrable
scale bounds remove smoothing. Quantitative Gaussian approximation then
combines with self-similar concentration to give an L2 density. Splitting
independent even and odd digits gives continuity at the original parameter.

All arithmetic, entropy, packing, Fourier, Gaussian and concentration inputs
needed for the working criterion and both appendices are contained in the
library. No external theorem is inserted as an axiom. Polynomial squaring
identities preserve the exact degree and Mahler-measure relationships used by
the main criterion. The integer threshold 588 is the exact threshold for the
stated sufficient rational inequality, not a claim that smaller parameters
cannot have continuous densities.

## Reuse and verification

The development adapts the cumulative LpSelfSimilar and BernoulliCubic library,
with additional revised statements and a migration to Lean's module system.
[Provenance](provenance/README.md) separates source reuse, module visibility
changes and substantive proof changes. Prior declarations remain available.

The default build covers all authored proof modules. The environment-based
[Verification.lean](Verification.lean) audits every imported authored declaration,
including generated declarations, and rejects nonstandard axioms. Strict
comparison and independent kernel checks separately establish the public
Challenge/Solution correspondence. Semantic review checks constants, quantifiers,
ordinary definitions and endpoint conditions; an axiom list alone does not do so.
Exact completed checks and their source snapshots are recorded in [verification](verification/README.md).

Background survey results and unrelated applications cited in the papers are not
additional formalization targets. Automated review is not independent human
peer review, and local verification does not assert registry acceptance.
