module

public import LpSelfSimilar.Analysis.VectorMeasureConvolution
public import LpSelfSimilar.Probability.PMFMixture
public import Mathlib.MeasureTheory.Group.IntegralConvolution

@[expose] public section

/-!
# Finite label mixtures acting on complex kernels

Measure convolution and the original finite label mixture act on the actual
integral of translates. Boundedness justifies pointwise integrability, while
the joint translation integral supplies the integrated norm estimate.
-/

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal

namespace LpSelfSimilar.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Every translate of a bounded continuous function is integrable against a finite measure. -/
theorem integrable_vector_translate_of_bounded (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → E} (hc : Continuous f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) (x : ℝ) :
    Integrable (fun y ↦ f (x - y)) μ := by
  apply (integrable_const C).mono' (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact ae_of_all _ (fun y ↦ hb (x - y))

/-- Averaging a bounded continuous vector-valued function preserves continuity. -/
theorem continuous_measureFunctionConvolution_of_bounded
    (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → E}
    (hc : Continuous f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    Continuous (measureFunctionConvolution μ f) := by
  apply continuous_of_dominated (bound := fun _ ↦ C)
  · exact fun x ↦ (integrable_vector_translate_of_bounded μ hc hb x).aestronglyMeasurable
  · exact fun x ↦ ae_of_all _ (fun y ↦ hb (x - y))
  · exact integrable_const C
  · exact ae_of_all _ (fun y ↦ hc.comp (continuous_id.sub continuous_const))

/-- Associativity of the actual finite-measure convolution action. -/
theorem measureFunctionConvolution_conv (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : ℝ → E}
    (hc : Continuous f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) (x : ℝ) :
    measureFunctionConvolution (μ ∗ ν) f x =
      measureFunctionConvolution μ (measureFunctionConvolution ν f) x := by
  rw [measureFunctionConvolution,
    integral_conv (integrable_vector_translate_of_bounded (μ ∗ ν) hc hb x)]
  apply integral_congr_ae
  apply ae_of_all
  intro y
  change (∫ z, f (x - (y + z)) ∂ν) = ∫ z, f (x - y - z) ∂ν
  congr 1
  ext z
  congr 1
  ring

/-- Exact vector integration against the original finite label mixture. -/
theorem integral_pmfMixture_vector {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (μ : Ω → Measure ℝ) {f : ℝ → E} (hf : ∀ a, Integrable f (μ a)) :
    (∫ x, f x ∂pmfMixture p μ) = ∑ a, (p a).toReal • ∫ x, f x ∂μ a := by
  unfold pmfMixture finiteMixture
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, ENNReal.coe_toReal]
    rfl
  · intro a ha
    exact (hf a).smul_measure (by simp)

/-- The actual mixture convolution is the original weighted sum of conditional convolutions. -/
theorem measureFunctionConvolution_pmfMixture {Ω : Type*} [Fintype Ω]
    (p : PMF Ω) (μ : Ω → Measure ℝ) [∀ a, IsFiniteMeasure (μ a)]
    {f : ℝ → E} (hc : Continuous f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) (x : ℝ) :
    measureFunctionConvolution (pmfMixture p μ) f x =
      ∑ a, (p a).toReal • measureFunctionConvolution (μ a) f x :=
  integral_pmfMixture_vector p μ (fun a ↦ integrable_vector_translate_of_bounded (μ a) hc hb x)

/-- Finite mixing contracts the expected conditional convolution L1 norm. -/
theorem integral_norm_measureFunctionConvolution_pmfMixture_le
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (μ : Ω → Measure ℝ) [∀ a, IsFiniteMeasure (μ a)]
    {f : ℝ → E} (hc : Continuous f) (hf : Integrable f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, ‖measureFunctionConvolution (pmfMixture p μ) f x‖) ≤
      ∫ a, (∫ x, ‖measureFunctionConvolution (μ a) f x‖) ∂p.toMeasure := by
  haveI : IsFiniteMeasure (pmfMixture p μ) := by
    unfold pmfMixture
    infer_instance
  have hi a := (integrable_measureFunctionConvolution (μ a) hc hf).norm
  have hb' x : ‖measureFunctionConvolution (pmfMixture p μ) f x‖ ≤
      ∑ a, (p a).toReal * ‖measureFunctionConvolution (μ a) f x‖ := by
    rw [measureFunctionConvolution_pmfMixture p μ hc hb x]
    calc
      _ ≤ ∑ a, ‖(p a).toReal • measureFunctionConvolution (μ a) f x‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have h := integral_mono (integrable_measureFunctionConvolution (pmfMixture p μ) hc hf).norm
    (integrable_finsetSum _ (fun a ha ↦ (hi a).const_mul (p a).toReal)) hb'
  rw [integral_finsetSum Finset.univ (fun a ha ↦ (hi a).const_mul (p a).toReal)] at h
  simp only [integral_const_mul] at h
  simpa only [PMF.integral_eq_sum, smul_eq_mul] using h

end LpSelfSimilar.Analysis
