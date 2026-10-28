# Source notes and proof variants

The selected mathematical statements retain the hypotheses, constants and
endpoints of the Kittle–Kogler sources. This file records changes to supporting
arguments and editorial references; the full development audit is kept separately.

- The revised weak reverse Hölder lemma has `C=18^d` and no factor two in the
  logarithmic denominator. The older `21^d` result remains available but does
  not replace the revised lemma. A dyadic stopping-ball proof with an eightfold
  enlargement has sufficient contraction for the exact new exponent. A separate
  six-adic construction and triple cover retain the source's precise level
  recurrence `gamma=2*6^d*eta` and endpoint ratio `2*(1/3)^d`. The intermediate
  volume fraction `2*2^d/A` is absorbed by the constant `18^d`. These constructions
  use discrete stopping radii in place of maximal-radius selection.
- The exponent-100 theorem's endpoint is obtained from the proved
  gap condition `(1-lambda)*B^100<2`, since the stated hypothesis gives `<=1`.
- The bounded-approximation proof retains a valid estimate from the older
  reverse Hölder constants. Its displayed intermediate exponent need not be
  the revised lemma's exact exponent; the claimed final quantitative gain is
  checked directly.
- The higher-to-first Gaussian detail estimate treats `k=1` separately. The
  integration-by-parts formula with `(k-2)!` belongs to the higher-order case.
- The integrating-detail proof's reference to Lemma 3.5 refers to the preceding
  higher-to-first estimate, Lemma 3.4. Editorial placeholders and cross-reference
  typos do not add mathematical hypotheses.
- Finite stopping words replace informal stopping-time notation. The proof uses
  the averaged pushforward law explicitly; a random pushforward need not equal
  the stationary measure for every outcome.

The threshold 588 characterizes the sufficient rational inequality in the
numerator-one family. It is not a necessary threshold for continuity.
