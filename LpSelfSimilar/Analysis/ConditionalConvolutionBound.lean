module

public import LpSelfSimilar.Analysis.VectorConvolutionMixture

@[expose] public section

/-!
# Conditional convolutions with an independent remainder and tail

The actual measure factorization retains its original finite label PMF. The
unused-digit probability law can be discarded from an L1 upper bound, while
the reserved tail stays inside every conditional convolution.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A probability convolution preserves any uniform norm bound. -/
theorem norm_measureFunctionConvolution_probability_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {f : ℝ → E}
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) (x : ℝ) :
    ‖measureFunctionConvolution μ f x‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y ↦ f (x - y))
    (ae_of_all _ (fun y ↦ hb (x - y)))
  simpa only [measureFunctionConvolution, measureReal_def, measure_univ,
    ENNReal.toReal_one, mul_one, one_mul] using h

/-- The original mixture with remainder and reserved tail is bounded by the conditional tail mean. -/
theorem integral_norm_mixture_remainder_tail_convolution_le
    {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (μ : Ω → Measure ℝ) [∀ a, IsProbabilityMeasure (μ a)]
    (η τ : Measure ℝ) [IsProbabilityMeasure η] [IsProbabilityMeasure τ]
    {f : ℝ → E} (hc : Continuous f) (hf : Integrable f)
    {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, ‖measureFunctionConvolution ((pmfMixture p μ ∗ η) ∗ τ) f x‖) ≤
      ∫ a, (∫ x, ‖measureFunctionConvolution (μ a ∗ τ) f x‖) ∂p.toMeasure := by
  let g := measureFunctionConvolution τ f
  have hgc : Continuous g := continuous_measureFunctionConvolution_of_bounded τ hc hb
  have hgi : Integrable g := integrable_measureFunctionConvolution τ hc hf
  have hgb : ∀ x, ‖g x‖ ≤ C := norm_measureFunctionConvolution_probability_le τ hb
  have he x : measureFunctionConvolution ((pmfMixture p μ ∗ η) ∗ τ) f x =
      measureFunctionConvolution η (measureFunctionConvolution (pmfMixture p μ) g) x := by
    rw [conv_comm (pmfMixture p μ) η, conv_assoc,
      measureFunctionConvolution_conv η (pmfMixture p μ ∗ τ) hc hb]
    congr 1
    funext y
    exact measureFunctionConvolution_conv (pmfMixture p μ) τ hc hb y
  simp_rw [he]
  have h₁ := integral_norm_measureFunctionConvolution_probability_le η
    (continuous_measureFunctionConvolution_of_bounded (pmfMixture p μ) hgc hgb)
    (integrable_measureFunctionConvolution (pmfMixture p μ) hgc hgi)
  have h₂ := integral_norm_measureFunctionConvolution_pmfMixture_le p μ hgc hgi hgb
  have he' a x : measureFunctionConvolution (μ a) g x =
      measureFunctionConvolution (μ a ∗ τ) f x :=
    (measureFunctionConvolution_conv (μ a) τ hc hb x).symm
  simpa only [he'] using h₁.trans h₂

end LpSelfSimilar.Analysis
