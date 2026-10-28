module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact integer shifts into a geometric band

Taking the ceiling of the logarithmic ratio moves any positive number into
`(theta*b,b]`. Integer shifts are essential at arbitrary scales. A separate
lemma proves nonnegativity when the original number is at least the upper
endpoint, which is the condition later supplied by digit packing.
-/

namespace LpSelfSimilar.Analysis

/-- The first integer shift whose scaled value is at most `b`. -/
noncomputable def geometricBandShift (θ x b : ℝ) : ℤ :=
  ⌈Real.log (x / b) / (-Real.log θ)⌉

/-- The ceiling places the value in the geometric band, retaining its exact endpoints. -/
theorem geometricBandShift_spec {θ x b : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hx : 0 < x) (hb : 0 < b) :
    θ * b < θ ^ geometricBandShift θ x b * x ∧
      θ ^ geometricBandShift θ x b * x ≤ b := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hpow : 0 < θ ^ geometricBandShift θ x b := zpow_pos hθ0 _
  have hceil : Real.log (x / b) / (-Real.log θ) ≤
      (geometricBandShift θ x b : ℝ) := Int.le_ceil _
  have hceil' : (geometricBandShift θ x b : ℝ) <
      Real.log (x / b) / (-Real.log θ) + 1 := Int.ceil_lt_add_one _
  have hupper := (div_le_iff₀ hχ).mp hceil
  have hlower := mul_lt_mul_of_pos_right hceil' hχ
  rw [add_mul, div_mul_cancel₀ _ hχ.ne', one_mul] at hlower
  rw [Real.log_div hx.ne' hb.ne'] at hupper hlower
  constructor
  · apply (Real.log_lt_log_iff (mul_pos hθ0 hb) (mul_pos hpow hx)).mp
    rw [Real.log_mul hθ0.ne' hb.ne', Real.log_mul hpow.ne' hx.ne', Real.log_zpow]
    nlinarith
  · apply (Real.log_le_log_iff (mul_pos hpow hx) hb).mp
    rw [Real.log_mul hpow.ne' hx.ne', Real.log_zpow]
    nlinarith

/-- If the starting value is at least the upper endpoint, no negative shift is needed. -/
theorem geometricBandShift_nonneg {θ x b : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hb : 0 < b) (hbx : b ≤ x) :
    0 ≤ geometricBandShift θ x b := by
  apply Int.ceil_nonneg
  apply div_nonneg
  · exact Real.log_nonneg ((one_le_div hb).mpr hbx)
  · exact (neg_pos.mpr (Real.log_neg hθ0 hθ1)).le

/-- Multiplying the starting value by an integer geometric power translates the shift exactly. -/
theorem geometricBandShift_mul_zpow {θ x b : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hx : 0 < x) (hb : 0 < b) (m : ℤ) :
    geometricBandShift θ (θ ^ m * x) b = geometricBandShift θ x b - m := by
  have hlog : Real.log θ ≠ 0 := (Real.log_neg hθ0 hθ1).ne
  have he : Real.log ((θ ^ m * x) / b) / (-Real.log θ) =
      Real.log (x / b) / (-Real.log θ) - (m : ℝ) := by
    rw [Real.log_div (mul_pos (zpow_pos hθ0 m) hx).ne' hb.ne',
      Real.log_mul (zpow_pos hθ0 m).ne' hx.ne', Real.log_zpow,
      Real.log_div hx.ne' hb.ne']
    field_simp
    <;> ring
  unfold geometricBandShift
  rw [he, Int.ceil_sub_intCast]

end LpSelfSimilar.Analysis
