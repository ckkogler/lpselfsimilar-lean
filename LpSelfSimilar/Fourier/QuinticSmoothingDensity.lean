module

public import LpSelfSimilar.Fourier.QuinticSmoothingLimit
public import LpSelfSimilar.Fourier.QuinticKernelTransforms
public import LpSelfSimilar.Analysis.KernelDensityLimit

@[expose] public section

/-!
# Removing quintic smoothing and identifying the density

The actual mass-one kernel converges weakly to the original measure. Its
previously constructed L1 limit is therefore a nonnegative density. Passing to
an everywhere nonnegative measurable representative preserves the exact error
bound by the full integrated detail.
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis
open scoped ENNReal

namespace LpSelfSimilar.Fourier

/-- Integrable actual quintic detail gives the original measure a nonnegative density and error bound. -/
theorem exists_quintic_smoothing_density (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {ε χ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hχ : 0 < χ)
    (hi : IntegrableOn (fun r =>
      (∫ x, ‖measureFunctionConvolution μ (rescaledKernel r (quinticDetailKernel ε)) x‖) / r)
      (Ioc 0 χ)) :
    ∃ f : ℝ → ℝ, Measurable f ∧ Integrable f ∧ (∀ x, 0 ≤ f x) ∧
      μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
      (∫ x, |f x - measureFunctionConvolution μ
        (rescaledKernel χ (quinticSmoothingKernel ε)) x|) ≤
        ∫ r in Ioc 0 χ,
          (∫ x, ‖measureFunctionConvolution μ (rescaledKernel r (quinticDetailKernel ε)) x‖) / r := by
  obtain ⟨f, hfm, hfi, hlim, herr⟩ := exists_quintic_smoothing_L1_limit μ hε hχ hi
  obtain ⟨g, hgm, hgi, hg0, hge, he⟩ := exists_nonnegative_density_of_kernel_L1_limit μ
    (continuous_quinticSmoothingKernel hε) (integrable_quinticSmoothingKernel hε)
    (integral_quinticSmoothingKernel hε hε1) (reciprocalScaleSequence_pos hχ)
    (tendsto_reciprocalScaleSequence χ) hfm hfi hlim
  refine ⟨g, hgm, hgi, hg0, he, ?_⟩
  calc
    _ = ∫ x, |f x - measureFunctionConvolution μ
        (rescaledKernel χ (quinticSmoothingKernel ε)) x| := by
      apply integral_congr_ae
      exact hge.mono (fun x hx => by dsimp only; rw [hx])
    _ ≤ _ := herr

end LpSelfSimilar.Fourier
