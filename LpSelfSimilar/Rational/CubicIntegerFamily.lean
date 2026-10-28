module

public import LpSelfSimilar.Rational.CubicContinuity
public import LpSelfSimilar.Analysis.CubicRationalThreshold

@[expose] public section

/-!
# Continuous densities for every integer denominator at least 588

The proved exact threshold supplies the numerator-one cubic inequality.
Positivity, coprimality and the parameter interval are derived, so the final
family theorem assumes only n>=588. Both natural and integer presentations
are provided, with explicit nonnegative compact density representations.
-/

open MeasureTheory Real

namespace LpSelfSimilar

/-- Every natural denominator n>=588 gives a nonnegative continuous compactly supported density. -/
theorem bernoulli_convolution_one_sub_inv_continuous_density_cubic (n : ℕ) (hn : 588 ≤ n) :
    ∃ f : ℝ → ℝ, (∀ y, 0 ≤ f y) ∧ Continuous f ∧ HasCompactSupport f ∧
      Bernoulli.convolution (1 - 1 / (n : ℝ)) =
        volume.withDensity (fun y => ENNReal.ofReal (f y)) := by
  have hn0 : 0 < n := by omega
  have hnr : (0 : ℝ) < n := by positivity
  have hnlarge : (588 : ℝ) ≤ n := by exact_mod_cast hn
  have hsmall : (1 : ℝ) ≤ (n : ℝ) / (2 + log (n : ℝ)) ^ 3 :=
    (Analysis.cubicRationalAllowance_integer_threshold n).mpr hn
  have hinv : (1 : ℝ) / n < 1 / 2 := (div_lt_iff₀ hnr).mpr (by linarith)
  have hinv0 : (0 : ℝ) < 1 / n := by positivity
  have hhalf : (1 : ℝ) / 2 < 1 - 1 / (n : ℝ) := by linarith
  have hone : 1 - 1 / (n : ℝ) < 1 := by linarith
  simpa only [Nat.cast_one] using rational_bernoulli_convolution_continuous_density_cubic
    1 n (by norm_num) hn0 (by simp)
    (by simpa only [Nat.cast_one] using hhalf)
    (by simpa only [Nat.cast_one] using hone)
    (by simpa only [Nat.cast_one] using hsmall)

/-- The same family stated for integers, with every hypothesis derived from n>=588. -/
theorem bernoulli_convolution_one_sub_inv_continuous_density_cubic_int (n : ℤ) (hn : 588 ≤ n) :
    ∃ f : ℝ → ℝ, (∀ y, 0 ≤ f y) ∧ Continuous f ∧ HasCompactSupport f ∧
      Bernoulli.convolution (1 - 1 / (n : ℝ)) =
        volume.withDensity (fun y => ENNReal.ofReal (f y)) := by
  have hn0 : 0 ≤ n := by omega
  have hnat : 588 ≤ n.toNat := by omega
  have he : (n.toNat : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn0
  simpa only [he] using bernoulli_convolution_one_sub_inv_continuous_density_cubic n.toNat hnat

end LpSelfSimilar
