module

public import LpSelfSimilar.Analysis.KernelMixtureConvolution
public import LpSelfSimilar.Gaussian.HigherDetail

@[expose] public section

/-!
Convexity and measurability of Gaussian detail under arbitrary probability-kernel
mixtures. This extends the earlier finite-mixture statements to general
conditioning spaces. Joint L1 integrability is proved by the reusable convolution
module; no conditional-density regularity is assumed.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real

namespace LpSelfSimilar.Gaussian

lemma stronglyMeasurable_higherDetail_kernel {Ω : Type*} [MeasurableSpace Ω]
    (κ : Kernel Ω ℝ) [IsSFiniteKernel κ] (k : ℕ) (r : ℝ) :
    StronglyMeasurable (fun ω ↦ higherDetail (κ ω) k r) := by
  have hm := stronglyMeasurable_averageTranslate_kernel κ
    (continuous_higherKernel_space k ((k : ℝ) * r ^ 2))
  simpa only [higherDetail, higherSmooth, Real.norm_eq_abs] using
    hm.norm.integral_prod_right.const_mul (r ^ (2 * k) * detailNormalization ^ k)

lemma integrable_higherDetail_kernel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    Integrable (fun ω ↦ higherDetail (κ ω) k r) P := by
  apply (integrable_const (1 : ℝ)).mono'
    (stronglyMeasurable_higherDetail_kernel κ k r).aestronglyMeasurable
  exact ae_of_all _ (fun ω ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (higherDetail_nonneg _ _ _)]
    exact higherDetail_le_one (κ ω) hk hr)

lemma higherDetail_kernel_comp_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    {k : ℕ} (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    higherDetail (κ ∘ₘ P) k r ≤ ∫ ω, higherDetail (κ ω) k r ∂P := by
  have hy : 0 < (k : ℝ) * r ^ 2 := by positivity
  obtain ⟨C, _, hb⟩ := exists_uniform_bound_higherKernel k hy
  have h := integral_abs_averageTranslate_kernel_comp_le P κ
    (continuous_higherKernel_space k _) (integrable_higherKernel k hy) (hb _ le_rfl)
  unfold higherDetail higherSmooth
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left h (by positivity [detailNormalization_pos])

lemma detail_kernel_comp_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    {r : ℝ} (hr : 0 < r) :
    detail (κ ∘ₘ P) r ≤ ∫ ω, detail (κ ω) r ∂P := by
  simpa only [higherDetail_one _ hr] using
    higherDetail_kernel_comp_le P κ (by norm_num : 0 < (1 : ℕ)) hr

end LpSelfSimilar.Gaussian
