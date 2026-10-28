module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-!
# Convolution of a finite measure with a vector-valued function

The measure acts by the actual integral of translates. Translation invariance
and Fubini give an L1 contraction for probability measures without any density
assumption on the measure. This extends the preserved real-valued API to the
complex kernels used for angular Fourier inversion.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Actual convolution of a measure and a vector-valued function. -/
noncomputable def measureFunctionConvolution (μ : Measure ℝ) (f : ℝ → E) (x : ℝ) : E :=
  ∫ y, f (x - y) ∂μ

/-- The joint translation integrand is integrable for a continuous L1 function. -/
theorem integrable_vector_translation_product (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → E} (hc : Continuous f) (hf : Integrable f) :
    Integrable (fun p : ℝ × ℝ ↦ f (p.2 - p.1)) (μ.prod volume) := by
  apply (integrable_prod_iff (hc.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun y ↦ hf.comp_sub_right y)
  · change Integrable (fun y ↦ ∫ x, ‖f (x - y)‖) μ
    simp_rw [integral_sub_right_eq_self (fun x ↦ ‖f x‖)]
    exact integrable_const _

/-- Finite-measure convolution preserves integrability of continuous L1 functions. -/
theorem integrable_measureFunctionConvolution (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → E} (hc : Continuous f) (hf : Integrable f) :
    Integrable (measureFunctionConvolution μ f) :=
  (integrable_vector_translation_product μ hc hf).integral_prod_right

/-- The exact mass factor in the measure-function convolution norm bound. -/
theorem integral_norm_measureFunctionConvolution_le (μ : Measure ℝ) [IsFiniteMeasure μ]
    {f : ℝ → E} (hc : Continuous f) (hf : Integrable f) :
    (∫ x, ‖measureFunctionConvolution μ f x‖) ≤ μ.real Set.univ * ∫ x, ‖f x‖ := by
  have h := integrable_vector_translation_product μ hc hf
  calc
    _ ≤ ∫ x, ∫ y, ‖f (x - y)‖ ∂μ := by
      apply integral_mono (integrable_measureFunctionConvolution μ hc hf).norm h.norm.integral_prod_right
      intro x
      exact norm_integral_le_integral_norm _
    _ = ∫ y, (∫ x, ‖f (x - y)‖) ∂μ :=
      integral_integral_swap (f := fun x y ↦ ‖f (x - y)‖) h.norm.swap
    _ = _ := by
      simp_rw [integral_sub_right_eq_self (fun x ↦ ‖f x‖)]
      rw [integral_const, smul_eq_mul]

/-- Convolution by any probability measure contracts the L1 norm. -/
theorem integral_norm_measureFunctionConvolution_probability_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → E}
    (hc : Continuous f) (hf : Integrable f) :
    (∫ x, ‖measureFunctionConvolution μ f x‖) ≤ ∫ x, ‖f x‖ := by
  simpa using integral_norm_measureFunctionConvolution_le μ hc hf

/-- Translation invariance applies to the full norm integral, including complex kernels. -/
theorem integral_norm_translate_eq (f : ℝ → E) (y : ℝ) :
    (∫ x, ‖f (x - y)‖) = ∫ x, ‖f x‖ :=
  integral_sub_right_eq_self (fun x ↦ ‖f x‖) y

end LpSelfSimilar.Analysis
