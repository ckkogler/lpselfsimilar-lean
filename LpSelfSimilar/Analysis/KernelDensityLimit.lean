module

public import LpSelfSimilar.Analysis.KernelWeakConvergence
public import LpSelfSimilar.Analysis.SignedDensityIdentification
public import LpSelfSimilar.Analysis.BoundedTestLimit

@[expose] public section

/-!
# Density identification for an L1 limit of signed kernel smoothings

Weak approximation and convergence in L1 give the same bounded continuous test
integrals. Positivity of the original measure then forces the signed limit to
be nonnegative almost everywhere. Its positive part is a measurable everywhere
nonnegative representative of the actual density, equal almost everywhere to
the original L1 limit.
-/

open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace LpSelfSimilar.Analysis

/-- The signed L1 limit of actual mass-one kernel smoothings represents the original measure. -/
theorem ae_nonneg_and_eq_withDensity_of_kernel_L1_limit
    (μ : Measure ℝ) [IsFiniteMeasure μ] {k : ℝ → ℝ}
    (hkc : Continuous k) (hki : Integrable k) (hkm : (∫ x, k x) = 1)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    {f : ℝ → ℝ} (hfm : Measurable f) (hfi : Integrable f)
    (hlim : Tendsto (fun n => ∫ x,
      |measureFunctionConvolution μ (rescaledKernel (r n) k) x - f x|) atTop (𝓝 0)) :
    (∀ᵐ x, 0 ≤ f x) ∧ μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  apply ae_nonneg_and_eq_withDensity_of_bounded_tests μ hfm hfi
  intro v
  have hweak := tendsto_integral_bounded_test_convolution_rescaledKernel μ v hkc hki hkm hr hrlim
  have hstrong := tendsto_integral_bounded_mul_of_L1
    (fun n => integrable_measureFunctionConvolution μ (continuous_rescaledKernel hkc (r n))
      (integrable_rescaledKernel hki (hr n).ne')) hfi
    v.continuous.aestronglyMeasurable (norm_nonneg v)
    (ae_of_all _ (fun x => v.norm_coe_le_norm x)) hlim
  exact tendsto_nhds_unique hweak hstrong

/-- An everywhere nonnegative measurable density is obtained from the actual signed L1 limit. -/
theorem exists_nonnegative_density_of_kernel_L1_limit
    (μ : Measure ℝ) [IsFiniteMeasure μ] {k : ℝ → ℝ}
    (hkc : Continuous k) (hki : Integrable k) (hkm : (∫ x, k x) = 1)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    {f : ℝ → ℝ} (hfm : Measurable f) (hfi : Integrable f)
    (hlim : Tendsto (fun n => ∫ x,
      |measureFunctionConvolution μ (rescaledKernel (r n) k) x - f x|) atTop (𝓝 0)) :
    ∃ g : ℝ → ℝ, Measurable g ∧ Integrable g ∧ (∀ x, 0 ≤ g x) ∧
      g =ᵐ[volume] f ∧ μ = volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
  obtain ⟨hf0, he⟩ := ae_nonneg_and_eq_withDensity_of_kernel_L1_limit
    μ hkc hki hkm hr hrlim hfm hfi hlim
  let g : ℝ → ℝ := fun x => max (f x) 0
  have hge : g =ᵐ[volume] f := hf0.mono (fun x hx => max_eq_left hx)
  refine ⟨g, hfm.max measurable_const, hfi.congr hge.symm, fun x => le_max_right _ _, hge, ?_⟩
  rw [he]
  apply withDensity_congr_ae
  exact hge.symm.mono (fun x hx => congrArg ENNReal.ofReal hx)

end LpSelfSimilar.Analysis
