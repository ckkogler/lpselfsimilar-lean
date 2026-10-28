module

public import LpSelfSimilar.Bernoulli.EntropyRate
public import LpSelfSimilar.Algebraic.StrongDigitEntropy

@[expose] public section

/-!
# Algebraic Bernoulli entropy rates and Gaussian comparison

The entropy rate here is the proved limit of the actual finite digit-law
entropies. Nonunits have rate log(2), and the canonical contracting-unit
comparison bounds the rate below by every Gaussian information increment.
The positive-amplitude family is nonempty and bounded above, so its real
supremum gives the written Gaussian comparison without a default-value issue.
The exact profile and the coefficients 3/10 and 1/2 pass to this same rate.
-/

open Real Set
open LpSelfSimilar.Bernoulli LpSelfSimilar.Gaussian

namespace LpSelfSimilar.Algebraic

/-- Outside the algebraic units every nonzero parameter has full binary entropy rate. -/
theorem entropyRate_eq_log_two_of_not_isAlgebraicUnit {x : ℝ} (hx0 : x ≠ 0)
    (hx : ¬ IsAlgebraicUnit x) : entropyRate x = log 2 := by
  apply entropyRate_eq_of_digitEntropy_eq
  intro n
  exact digit_entropy_of_not_isAlgebraicUnit hx0 hx n

/-- Each scalar Gaussian information increment is bounded by the actual unit entropy rate. -/
theorem unit_entropyRate_ge_binary_information {x : ℝ} (hx : IsAlgebraicUnit x)
    (hx0 : 0 < x) (hx1 : x < 1) (u : ℝ) :
    binaryGaussianInformation (u * mahlerMeasure x) - binaryGaussianInformation u ≤
      entropyRate x := by
  apply le_entropyRate_of_mul_le
  intro n
  exact unit_digit_entropy_ge_binary_information hx hx0 hx1 u n

/-- The positive-amplitude information increments form a genuinely bounded family. -/
theorem unit_information_gains_bddAbove {x : ℝ} (hx : IsAlgebraicUnit x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    BddAbove ((fun u : ℝ => binaryGaussianInformation (u * mahlerMeasure x) -
      binaryGaussianInformation u) '' Ioi 0) := by
  refine ⟨entropyRate x, ?_⟩
  rintro _ ⟨u, _, rfl⟩
  exact unit_entropyRate_ge_binary_information hx hx0 hx1 u

/-- The full positive-amplitude supremum comparison for the actual limiting entropy rate. -/
theorem unit_entropyRate_ge_sup_information {x : ℝ} (hx : IsAlgebraicUnit x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    sSup ((fun u : ℝ => binaryGaussianInformation (u * mahlerMeasure x) -
      binaryGaussianInformation u) '' Ioi 0) ≤ entropyRate x := by
  apply csSup_le
  · exact ⟨_, ⟨1, by norm_num, rfl⟩⟩
  · rintro _ ⟨u, _, rfl⟩
    exact unit_entropyRate_ge_binary_information hx hx0 hx1 u

/-- Reciprocal amplitudes give the exact Gaussian profile at the logarithmic Mahler measure. -/
theorem unit_entropyRate_ge_gaussianEntropyProfile {x : ℝ} (hx : IsAlgebraicUnit x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    Analysis.gaussianEntropyProfile (log (mahlerMeasure x)) ≤ entropyRate x := by
  have ha : IsAlgebraic ℚ x := (hx.2.1.tower_top (A := ℚ)).isAlgebraic
  have hM := one_lt_mahlerMeasure ha hx0 hx1
  have hpos : 0 < mahlerMeasure x := zero_lt_one.trans hM
  have hscale : exp (-log (mahlerMeasure x) / 2) * mahlerMeasure x =
      exp (log (mahlerMeasure x) / 2) := by
    conv_lhs => rhs; rw [← exp_log hpos]
    rw [← exp_add]
    congr 1 <;> ring
  have h := unit_entropyRate_ge_binary_information hx hx0 hx1
    (exp (-log (mahlerMeasure x) / 2))
  rw [hscale] at h
  exact (gaussianEntropyProfile_le_information_increment (log_nonneg hM.le)).trans h

/-- The exact uniform coefficient 3/10 also bounds the actual limiting entropy rate. -/
theorem entropyRate_three_tenths_lower {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (3 / 10 : ℝ) * min 1 (log (mahlerMeasure x)) ≤ entropyRate x := by
  apply le_entropyRate_of_mul_le
  intro n
  exact digit_entropy_three_tenths_lower hx hx0 hx1 n

/-- At logarithmic Mahler measure at least two, the actual rate is at least one half. -/
theorem entropyRate_half_lower {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) (hm : 2 ≤ log (mahlerMeasure x)) :
    (1 / 2 : ℝ) ≤ entropyRate x := by
  apply le_entropyRate_of_mul_le
  intro n
  exact digit_entropy_half_lower hx hx0 hx1 hm n

/-- The exact piecewise cubic entropy coefficient is a lower bound for the same limit. -/
theorem entropyRate_ge_algebraicEntropyLowerBound {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : algebraicEntropyLowerBound x ≤ entropyRate x := by
  apply le_entropyRate_of_mul_le
  intro n
  exact digit_entropy_ge_algebraicEntropyLowerBound hx hx0 hx1 n

/-- Every positive contracting algebraic parameter has strictly positive entropy rate. -/
theorem entropyRate_pos {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : 0 < entropyRate x :=
  (algebraicEntropyLowerBound_pos hx hx0 hx1).trans_le
    (entropyRate_ge_algebraicEntropyLowerBound hx hx0 hx1)

end LpSelfSimilar.Algebraic
