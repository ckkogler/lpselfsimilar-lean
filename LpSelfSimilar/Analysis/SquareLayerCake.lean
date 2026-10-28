module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# The square layer-cake identity

The exact coefficient two comes from integrating the derivative 2*u of u^2.
This extended nonnegative identity does not presume that the second moment is
finite, so it can be used to prove that finiteness from a tail bound.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- The integral of the derivative of a square, including all real endpoints. -/
theorem integral_twice_id_zero (x : ℝ) : (∫ u in (0 : ℝ)..x, 2 * u) = x ^ 2 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-- The exact nonnegative square layer-cake formula, without a moment assumption. -/
theorem lintegral_sq_eq_twice_lintegral_superlevel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℝ} (hf : AEMeasurable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ^ 2 ∂μ =
      2 * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * μ {x | u < f x} := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul μ (Filter.Eventually.of_forall hf0) hf
    (g := fun u : ℝ => 2 * u)
    (fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact mul_nonneg (by norm_num) (le_of_lt hu))
  simp only [integral_twice_id_zero, ENNReal.ofReal_pow (hf0 _)] at h
  rw [h, ← lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)]
  apply lintegral_congr
  intro u
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  ring

end LpSelfSimilar.Analysis
