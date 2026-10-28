module

public import LpSelfSimilar.Analysis.MeasureConvolution
public import LpSelfSimilar.Analysis.IntegralRemainderEstimate
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-!
Convolution of an integrable continuous function against a general probability
kernel mixture. Joint measurability and L1 integrability justify averaging the
smoothed functions and interchanging their integrals. The conditioning space
is an arbitrary measurable space, with no finiteness or standard-Borel assumption.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace LpSelfSimilar

lemma stronglyMeasurable_averageTranslate_kernel {Ω : Type*} [MeasurableSpace Ω]
    (κ : Kernel Ω ℝ) [IsSFiniteKernel κ] {f : ℝ → ℝ} (hc : Continuous f) :
    StronglyMeasurable (fun p : Ω × ℝ ↦ averageTranslate (κ p.1) f p.2) := by
  have h : StronglyMeasurable (fun p : (Ω × ℝ) × ℝ ↦ f (p.1.2 - p.2)) :=
    hc.stronglyMeasurable.comp_measurable (measurable_fst.snd.sub measurable_snd)
  simpa only [Kernel.comap_apply, averageTranslate] using
    h.integral_kernel_prod_right' (κ := κ.comap Prod.fst measurable_fst)

lemma averageTranslate_kernel_comp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    {f : ℝ → ℝ} (hc : Continuous f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) (x : ℝ) :
    averageTranslate (κ ∘ₘ P) f x = ∫ ω, averageTranslate (κ ω) f x ∂P := by
  have hi : Integrable (fun z ↦ f (x - z)) (κ ∘ₘ P) := by
    apply (integrable_const C).mono' (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    exact ae_of_all _ (fun z ↦ by simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.sub_apply, id_eq] using hb (x - z))
  rw [Measure.comp_eq_comp_const_apply] at hi
  have h := ProbabilityTheory.Kernel.integral_comp hi
  simpa only [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply, averageTranslate] using h

lemma integrable_averageTranslate_kernel_product {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    {f : ℝ → ℝ} (hc : Continuous f) (hf : Integrable f volume) :
    Integrable (fun p : Ω × ℝ ↦ averageTranslate (κ p.1) f p.2) (P.prod volume) := by
  have hm := stronglyMeasurable_averageTranslate_kernel κ hc
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun ω ↦ integrable_averageTranslate (κ ω) hc hf)
  · apply (integrable_const (∫ x, |f x|)).mono' hm.norm.integral_prod_right.aestronglyMeasurable
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _))]
    have h := integral_abs_averageTranslate_le (κ ω) hc hf
    simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, one_mul] using h

/-- Convexity of the L1 norm under general probability-kernel mixing. -/
lemma integral_abs_averageTranslate_kernel_comp_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    {f : ℝ → ℝ} (hc : Continuous f) (hf : Integrable f volume)
    {C : ℝ} (hb : ∀ x, |f x| ≤ C) :
    (∫ x, |averageTranslate (κ ∘ₘ P) f x|) ≤
      ∫ ω, (∫ x, |averageTranslate (κ ω) f x|) ∂P := by
  simp_rw [averageTranslate_kernel_comp P κ hc hb]
  exact integral_abs_integral_le (integrable_averageTranslate_kernel_product P κ hc hf)

end LpSelfSimilar
