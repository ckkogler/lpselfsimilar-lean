module

public import LpSelfSimilar.Analysis.RescaledKernelDerivative
public import LpSelfSimilar.Analysis.RescaledKernelIntegrability
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Integrating the exact change of kernel scale

On a compact positive scale interval the continuous detail over scale is
integrable. The fundamental theorem of calculus, applied to the actual scale
derivative, gives the difference of the two rescaled smoothing kernels.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- Continuous detail kernels divided by scale are integrable on positive compact intervals. -/
theorem intervalIntegrable_rescaledKernel_div_scale {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    IntervalIntegrable (fun r => rescaledKernel r ψ x / r) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro r hr
  have hpos : 0 < r := ha.trans_le hr.1
  exact ((continuousAt_rescaledKernel_scale hψ hpos.ne' x).div continuousAt_id hpos.ne').continuousWithinAt

/-- The actual kernel difference is the integral of detail over scale. -/
theorem rescaledKernel_sub_eq_integral_detail {f ψ : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hψ : Continuous ψ)
    (hd : ∀ y, ψ y = f y + y * deriv f y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    rescaledKernel a f x - rescaledKernel b f x =
      ∫ r in a..b, rescaledKernel r ψ x / r := by
  have hi := intervalIntegrable_rescaledKernel_div_scale hψ ha hab x
  have hderiv : ∀ r ∈ uIcc a b,
      HasDerivAt (fun s => rescaledKernel s f x) (-(rescaledKernel r ψ x / r)) r := by
    intro r hr
    rw [uIcc_of_le hab] at hr
    have hpos : 0 < r := ha.trans_le hr.1
    simpa only [neg_div] using hasDerivAt_rescaledKernel_scale_of_detail hf hd hpos.ne' x
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi.neg
  rw [intervalIntegral.integral_neg] at he
  linarith

end LpSelfSimilar.Analysis
