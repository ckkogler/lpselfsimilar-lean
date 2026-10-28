module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

@[expose] public section

/-!
# A sharp endpoint quadrature error for Lipschitz functions

On an interval of length `h`, replacing a Lipschitz function by its value at the
right endpoint costs at most `K*h^2/2`. Integrating the pointwise distance to that
endpoint retains the factor one half needed in geometric phase averaging.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- The exact right-endpoint rectangle error for a real Lipschitz function. -/
theorem abs_right_endpoint_quadrature_error_le {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {a b : ℝ} (hab : a ≤ b) :
    |(b - a) * f b - ∫ x in a..b, f x| ≤ (K : ℝ) / 2 * (b - a) ^ 2 := by
  have hi : IntervalIntegrable f volume a b := hf.continuous.intervalIntegrable a b
  have he : (b - a) * f b - (∫ x in a..b, f x) = ∫ x in a..b, (f b - f x) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const, smul_eq_mul]
  rw [he]
  calc
    |∫ x in a..b, (f b - f x)| ≤ ∫ x in a..b, |f b - f x| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ x in a..b, (K : ℝ) * (b - x) := by
      apply intervalIntegral.integral_mono_on hab
        ((continuous_const.sub hf.continuous).abs.intervalIntegrable a b)
        ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable a b)
      intro x hx
      simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
      simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.2)] using hf.dist_le_mul b x
    _ = (K : ℝ) / 2 * (b - a) ^ 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (f := fun _ : ℝ ↦ b) (g := fun x : ℝ ↦ x)
          intervalIntegrable_const (continuous_id.intervalIntegrable a b),
        intervalIntegral.integral_const, integral_id, smul_eq_mul]
      ring

end LpSelfSimilar.Analysis
