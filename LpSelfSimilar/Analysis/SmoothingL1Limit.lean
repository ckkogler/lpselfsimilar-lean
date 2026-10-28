module

public import LpSelfSimilar.Analysis.ConvolvedKernelScale
public import LpSelfSimilar.Analysis.L1CauchyLimit
public import LpSelfSimilar.Analysis.PositiveScaleTailIntegral
public import LpSelfSimilar.Analysis.BoundedTestLimit

@[expose] public section

/-!
# An actual L1 limit from integrable detail at scale zero

The integrated scale identity bounds the distance between two smoothings by a
shrinking tail of the detail integral. Dominated convergence makes those tails
vanish, and L1 completeness supplies a measurable integrable limit. Its error
from the initial smoothing is bounded by the full detail integral. No sign or
density assumption is made about the limit or the smoothing kernel.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace LpSelfSimilar.Analysis

/-- Integrable detail yields a measurable L1 limit and its exact coarse-scale error bound. -/
theorem exists_smoothing_L1_limit_of_integrable_detail
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {φ ψ : ℝ → ℝ}
    (hφ : Differentiable ℝ φ) (hφi : Integrable φ)
    (hψ : Continuous ψ) (hψi : Integrable ψ)
    (hd : ∀ y, ψ y = φ y + y * deriv φ y)
    {Cφ Cψ : ℝ} (hφb : ∀ y, ‖φ y‖ ≤ Cφ) (hψb : ∀ y, ‖ψ y‖ ≤ Cψ)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hranti : Antitone r)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hi : IntegrableOn (fun s =>
      (∫ x, ‖measureFunctionConvolution μ (rescaledKernel s ψ) x‖) / s) (Ioc 0 (r 0))) :
    ∃ f : ℝ → ℝ, Measurable f ∧ Integrable f ∧
      Tendsto (fun n => ∫ x,
        |measureFunctionConvolution μ (rescaledKernel (r n) φ) x - f x|) atTop (𝓝 0) ∧
      (∫ x, |f x - measureFunctionConvolution μ (rescaledKernel (r 0) φ) x|) ≤
        ∫ s in Ioc 0 (r 0), (∫ x, ‖measureFunctionConvolution μ (rescaledKernel s ψ) x‖) / s := by
  let F (n : ℕ) : ℝ → ℝ := measureFunctionConvolution μ (rescaledKernel (r n) φ)
  let D (s : ℝ) : ℝ := (∫ x, ‖measureFunctionConvolution μ (rescaledKernel s ψ) x‖) / s
  let B (n : ℕ) : ℝ := ∫ s in Ioc 0 (r n), D s
  have hF (n : ℕ) : Integrable (F n) :=
    integrable_measureFunctionConvolution μ (continuous_rescaledKernel hφ.continuous (r n))
      (integrable_rescaledKernel hφi (hr n).ne')
  have hB : Tendsto B atTop (𝓝 0) :=
    tendsto_integral_Ioc_zero_of_antitone_scale hranti hrlim hi
  have hC : ∀ n m, n ≤ m → (∫ x, |F n x - F m x|) ≤ B n := by
    intro n m hnm
    have hdiff := integral_norm_convolution_rescaledKernel_sub_le μ hφ hψ hψi hd
      hφb hψb (hr m) (hranti hnm)
    have hdiff' : (∫ x, |F n x - F m x|) ≤ ∫ s in r m..r n, D s := by
      simpa only [F, D, Real.norm_eq_abs, abs_sub_comm] using hdiff
    apply hdiff'.trans
    rw [intervalIntegral.integral_of_le (hranti hnm)]
    have hiN : IntegrableOn D (Ioc 0 (r n)) :=
      hi.mono_set (Ioc_subset_Ioc le_rfl (hranti (Nat.zero_le n)))
    apply setIntegral_mono_set hiN
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact div_nonneg (integral_nonneg (fun x => norm_nonneg _)) hs.1.le
    · exact ae_of_all _ (fun s hs => ⟨(hr m).trans hs.1, hs.2⟩)
  obtain ⟨f, hfm, hfi, hlim⟩ := exists_measurable_L1_limit F hF B hB hC
  refine ⟨f, hfm, hfi, hlim, ?_⟩
  apply integral_abs_sub_le_of_L1_limit hF hfi (hF 0) hlim
  intro n
  simpa only [abs_sub_comm] using hC 0 n (Nat.zero_le n)

end LpSelfSimilar.Analysis
