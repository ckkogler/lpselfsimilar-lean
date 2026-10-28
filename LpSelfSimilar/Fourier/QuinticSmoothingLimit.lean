module

public import LpSelfSimilar.Fourier.QuinticKernelDerivatives
public import LpSelfSimilar.Fourier.QuinticKernelBounds
public import LpSelfSimilar.Analysis.SmoothingL1Limit
public import LpSelfSimilar.Analysis.ReciprocalScaleSequence

@[expose] public section

/-!
# L1 limits of the actual quintic smoothings

Every kernel hypothesis of the general convergence theorem is supplied by the
proved quintic construction. Only the actual detail integral is an input. The
limit is measurable and integrable, with error bounded by that integral;
identification with a nonnegative density is a separate measure-theoretic step.
-/

open MeasureTheory Set Filter
open LpSelfSimilar.Analysis
open scoped Topology

namespace LpSelfSimilar.Fourier

/-- Integrable actual quintic detail gives a measurable L1 limit with an exact error bound. -/
theorem exists_quintic_smoothing_L1_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ε χ : ℝ} (hε : 0 < ε) (hχ : 0 < χ)
    (hi : IntegrableOn (fun r =>
      (∫ x, ‖measureFunctionConvolution μ (rescaledKernel r (quinticDetailKernel ε)) x‖) / r)
      (Ioc 0 χ)) :
    ∃ f : ℝ → ℝ, Measurable f ∧ Integrable f ∧
      Tendsto (fun n => ∫ x,
        |measureFunctionConvolution μ
          (rescaledKernel (reciprocalScaleSequence χ n) (quinticSmoothingKernel ε)) x - f x|)
        atTop (𝓝 0) ∧
      (∫ x, |f x - measureFunctionConvolution μ
        (rescaledKernel χ (quinticSmoothingKernel ε)) x|) ≤
        ∫ r in Ioc 0 χ,
          (∫ x, ‖measureFunctionConvolution μ (rescaledKernel r (quinticDetailKernel ε)) x‖) / r := by
  obtain ⟨Cφ, hφb⟩ := exists_bound_quinticSmoothingKernel ε
  obtain ⟨Cψ, hψb⟩ := exists_bound_quinticDetailKernel ε
  have hi' : IntegrableOn (fun r =>
      (∫ x, ‖measureFunctionConvolution μ (rescaledKernel r (quinticDetailKernel ε)) x‖) / r)
      (Ioc 0 (reciprocalScaleSequence χ 0)) := by
    simpa only [reciprocalScaleSequence_zero] using hi
  simpa only [reciprocalScaleSequence_zero] using
    exists_smoothing_L1_limit_of_integrable_detail μ
      (fun x => (hasDerivAt_quinticSmoothingKernel hε x).differentiableAt)
      (integrable_quinticSmoothingKernel hε) (continuous_quinticDetailKernel hε)
      (integrable_quinticDetailKernel hε) (quinticDetailKernel_eq_add_mul_deriv hε)
      hφb hψb (reciprocalScaleSequence_pos hχ) (antitone_reciprocalScaleSequence hχ.le)
      (tendsto_reciprocalScaleSequence χ) hi'

end LpSelfSimilar.Fourier
