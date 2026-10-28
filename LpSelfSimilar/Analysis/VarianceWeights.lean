module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
A discrete telescoping estimate for Gaussian replacement weights. If a variance
increment is at most the current smoothing variance, its `y^(-5/2)` weight is
controlled by the drop in `y^(-3/2)`. No limiting integral is assumed.
-/

open Real

namespace LpSelfSimilar

private lemma sqrt_increment_weight {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 2 * a) :
    (b ^ 2 - a ^ 2) / a ^ 5 ≤ 24 * (a⁻¹ ^ 3 - b⁻¹ ^ 3) := by
  have hb0 := ha.trans_le hab
  have hc : b ^ 3 ≤ 8 * a ^ 3 := by
    have h := pow_le_pow_left₀ hb0.le hb 3
    nlinarith
  have hcoeff : (b + a) * b ^ 3 ≤ 24 * a ^ 2 * (b ^ 2 + a * b + a ^ 2) := by
    calc
      (b + a) * b ^ 3 ≤ (3 * a) * (8 * a ^ 3) :=
        mul_le_mul (by linarith) hc (pow_nonneg hb0.le 3) (by positivity)
      _ = 24 * a ^ 2 * a ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hcoeff (sub_nonneg.mpr hab)
  apply (div_le_iff₀ (pow_pos ha 5)).mpr
  apply (mul_le_mul_iff_left₀ (pow_pos hb0 3)).mp
  have he : 24 * (a⁻¹ ^ 3 - b⁻¹ ^ 3) * a ^ 5 * b ^ 3 =
      (b - a) * (24 * a ^ 2 * (b ^ 2 + a * b + a ^ 2)) := by
    field_simp
    <;> ring
  rw [he]
  convert hh using 1 <;> ring

lemma variance_increment_weight_le {y v : ℝ} (hy : 0 < y) (hv : 0 ≤ v) (hvy : v ≤ y) :
    v * (y⁻¹ ^ 2 / Real.sqrt y) ≤
      24 * (y⁻¹ / Real.sqrt y - (y + v)⁻¹ / Real.sqrt (y + v)) := by
  have hyv : 0 < y + v := by positivity
  have ha := Real.sqrt_pos.mpr hy
  have hb := Real.sqrt_pos.mpr hyv
  have hasq := Real.sq_sqrt hy.le
  have hbsq := Real.sq_sqrt hyv.le
  have hab : Real.sqrt y ≤ Real.sqrt (y + v) := Real.sqrt_le_sqrt (by linarith)
  have hb2 : Real.sqrt (y + v) ≤ 2 * Real.sqrt y := by nlinarith
  have h := sqrt_increment_weight ha hab hb2
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
