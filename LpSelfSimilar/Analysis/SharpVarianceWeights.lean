module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
A quantitative telescoping bound for Gaussian replacement weights. Keeping the
relation b^2 <= 2 a^2 between successive standard deviations gives constant two.
This strengthens the earlier constant-24 estimate without changing its proof.
-/

open Real

namespace LpSelfSimilar

private lemma sqrt_increment_weight_two {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbsq : b ^ 2 ≤ 2 * a ^ 2) :
    (b ^ 2 - a ^ 2) / a ^ 5 ≤ 2 * (a⁻¹ ^ 3 - b⁻¹ ^ 3) := by
  have hb := ha.trans_le hab
  have h1 := mul_le_mul_of_nonneg_right hbsq (sq_nonneg b)
  have h2 := mul_le_mul_of_nonneg_right hbsq (mul_nonneg ha.le hb.le)
  have hcoeff : (b + a) * b ^ 3 ≤ 2 * a ^ 2 * (b ^ 2 + a * b + a ^ 2) := by
    nlinarith [sq_nonneg (a ^ 2)]
  have hh := mul_le_mul_of_nonneg_left hcoeff (sub_nonneg.mpr hab)
  apply (div_le_iff₀ (pow_pos ha 5)).mpr
  apply (mul_le_mul_iff_left₀ (pow_pos hb 3)).mp
  have he : 2 * (a⁻¹ ^ 3 - b⁻¹ ^ 3) * a ^ 5 * b ^ 3 =
      (b - a) * (2 * a ^ 2 * (b ^ 2 + a * b + a ^ 2)) := by
    field_simp
    ring
  rw [he]
  convert hh using 1 <;> ring

lemma variance_increment_weight_le_two {y v : ℝ} (hy : 0 < y) (hv : 0 ≤ v)
    (hvy : v ≤ y) :
    v * (y⁻¹ ^ 2 / Real.sqrt y) ≤
      2 * (y⁻¹ / Real.sqrt y - (y + v)⁻¹ / Real.sqrt (y + v)) := by
  have hyv : 0 < y + v := by positivity
  have ha := Real.sqrt_pos.mpr hy
  have hb := Real.sqrt_pos.mpr hyv
  have hasq := Real.sq_sqrt hy.le
  have hbsq := Real.sq_sqrt hyv.le
  have hab : Real.sqrt y ≤ Real.sqrt (y + v) := Real.sqrt_le_sqrt (by linarith)
  have hbound : Real.sqrt (y + v) ^ 2 ≤ 2 * Real.sqrt y ^ 2 := by
    rw [hbsq, hasq]
    linarith
  have h := sqrt_increment_weight_two ha hab hbound
  have h1 : v * (y⁻¹ ^ 2 / Real.sqrt y) =
      (Real.sqrt (y + v) ^ 2 - Real.sqrt y ^ 2) / Real.sqrt y ^ 5 := by
    rw [hbsq, hasq]
    field_simp
    rw [show Real.sqrt y ^ 4 = y ^ 2 by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hasq]]
    ring
  have h2 : y⁻¹ / Real.sqrt y = (Real.sqrt y)⁻¹ ^ 3 := by
    field_simp
    nlinarith
  have h3 : (y + v)⁻¹ / Real.sqrt (y + v) = (Real.sqrt (y + v))⁻¹ ^ 3 := by
    field_simp
    nlinarith
  rw [h1, h2, h3]
  exact h

end LpSelfSimilar
