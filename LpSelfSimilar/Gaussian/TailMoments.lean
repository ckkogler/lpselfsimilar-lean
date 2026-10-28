module

public import LpSelfSimilar.Gaussian.EvenMoments
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# Exact Gaussian tail moments and the elementary tail bounds

The first moment has an explicit antiderivative. Its comparison with the
zeroth moment gives exp(-b^2)/(2*b). A second antiderivative relates the
quadratic tail to the zeroth tail, retaining b/2 + 1/(4*b). All integrability
and limits at infinity are proved for the actual Gaussian functions.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace LpSelfSimilar.Gaussian

/-- The Gaussian times the identity is integrable on the whole line. -/
theorem integrable_id_mul_exp_neg_sq :
    Integrable (fun x : ℝ => x * Real.exp (-(x ^ 2))) := by
  simpa only [neg_one_mul] using integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)

/-- Every nonnegative integer Gaussian moment tends to zero at positive infinity. -/
theorem tendsto_pow_mul_exp_neg_sq_zero (k : ℕ) :
    Tendsto (fun x : ℝ => x ^ k * Real.exp (-(x ^ 2))) atTop (𝓝 0) := by
  have h := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg (by norm_num : (0 : ℝ) < 1) (k : ℝ)).tendsto_zero_of_tendsto
    (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1 / 2 : ℝ) < 0)))
  simpa only [Real.rpow_natCast, neg_one_mul] using h

/-- The first Gaussian tail moment has its exact value at every real lower endpoint. -/
theorem integral_Ioi_id_mul_exp_neg_sq (b : ℝ) :
    (∫ u : ℝ in Ioi b, u * Real.exp (-(u ^ 2))) = Real.exp (-(b ^ 2)) / 2 := by
  have hd (u : ℝ) : HasDerivAt (fun x : ℝ => -(Real.exp (-(x ^ 2))) / 2)
      (u * Real.exp (-(u ^ 2))) u := by
    convert! ((((hasDerivAt_id u).pow 2).neg.exp).neg).div_const 2 using 1 <;>
      simp only [Pi.pow_apply, Pi.neg_apply, id_eq] <;> ring
  have ht : Tendsto (fun x : ℝ => -(Real.exp (-(x ^ 2))) / 2) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, neg_zero, zero_div] using
      ((tendsto_pow_mul_exp_neg_sq_zero 0).neg.div_const 2)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u hu => hd u)
    integrable_id_mul_exp_neg_sq.integrableOn ht (a := b)
  simpa only [zero_sub, neg_div, neg_neg] using h

/-- The zeroth Gaussian tail is bounded by its exact first-moment comparison. -/
theorem integral_Ioi_exp_neg_sq_le {b : ℝ} (hb : 0 < b) :
    (∫ u : ℝ in Ioi b, Real.exp (-(u ^ 2))) ≤ Real.exp (-(b ^ 2)) / (2 * b) := by
  have h0 : Integrable (fun u : ℝ => Real.exp (-(u ^ 2))) := by
    simpa only [Nat.mul_zero, pow_zero, one_mul] using integrable_gaussian_even_moment 0
  have hm := setIntegral_mono_on (s := Ioi b) h0.integrableOn
    (integrable_id_mul_exp_neg_sq.div_const b).integrableOn measurableSet_Ioi
    (fun u hu => by
      change Real.exp (-(u ^ 2)) ≤ (u * Real.exp (-(u ^ 2))) / b
      apply (le_div_iff₀ hb).mpr
      nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hu) (Real.exp_pos (-(u ^ 2))).le])
  rw [integral_div, integral_Ioi_id_mul_exp_neg_sq] at hm
  convert! hm using 1 <;> ring

/-- The quadratic Gaussian tail equals the boundary term plus half the zeroth tail. -/
theorem integral_Ioi_sq_mul_exp_neg_sq (b : ℝ) :
    (∫ u : ℝ in Ioi b, u ^ 2 * Real.exp (-(u ^ 2))) =
      (b / 2) * Real.exp (-(b ^ 2)) + (1 / 2 : ℝ) * ∫ u : ℝ in Ioi b, Real.exp (-(u ^ 2)) := by
  have h0 : Integrable (fun u : ℝ => Real.exp (-(u ^ 2))) := by
    simpa only [Nat.mul_zero, pow_zero, one_mul] using integrable_gaussian_even_moment 0
  have h2 : Integrable (fun u : ℝ => u ^ 2 * Real.exp (-(u ^ 2))) := by
    simpa only [Nat.mul_one] using integrable_gaussian_even_moment 1
  have hd (u : ℝ) : HasDerivAt (fun x : ℝ => -(x * Real.exp (-(x ^ 2))) / 2)
      (u ^ 2 * Real.exp (-(u ^ 2)) - (1 / 2 : ℝ) * Real.exp (-(u ^ 2))) u := by
    convert! (((hasDerivAt_id u).mul (((hasDerivAt_id u).pow 2).neg.exp)).neg).div_const 2 using 1 <;>
      simp only [Pi.pow_apply, Pi.neg_apply, id_eq] <;> ring
  have ht : Tendsto (fun x : ℝ => -(x * Real.exp (-(x ^ 2))) / 2) atTop (𝓝 0) := by
    simpa only [pow_one, neg_zero, zero_div] using
      ((tendsto_pow_mul_exp_neg_sq_zero 1).neg.div_const 2)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u hu => hd u)
    (h2.sub (h0.const_mul (1 / 2 : ℝ))).integrableOn ht (a := b)
  rw [integral_sub h2.integrableOn (h0.const_mul _).integrableOn, integral_const_mul] at h
  linarith

/-- The quadratic Gaussian tail has the exact boundary-plus-reciprocal upper bound. -/
theorem integral_Ioi_sq_mul_exp_neg_sq_le {b : ℝ} (hb : 0 < b) :
    (∫ u : ℝ in Ioi b, u ^ 2 * Real.exp (-(u ^ 2))) ≤
      (b / 2 + 1 / (4 * b)) * Real.exp (-(b ^ 2)) := by
  rw [integral_Ioi_sq_mul_exp_neg_sq]
  have h := mul_le_mul_of_nonneg_left (integral_Ioi_exp_neg_sq_le hb) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ ≤ (b / 2) * Real.exp (-(b ^ 2)) + (1 / 2 : ℝ) * (Real.exp (-(b ^ 2)) / (2 * b)) :=
      add_le_add le_rfl h
    _ = _ := by ring

end LpSelfSimilar.Gaussian
