module

public import LpSelfSimilar.Analysis.FunctionConvolution

@[expose] public section

/-!
Independent probability laws commute with convolution of integrable bounded
continuous kernels. This gives the factorization needed for the higher-detail
product inequality, including kernels which take both signs.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar

lemma averageTranslate_conv_functionConvolution (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {f g : ℝ → ℝ}
    (hfc : Continuous f) (hf : Integrable f volume) {C : ℝ} (hfb : ∀ x, |f x| ≤ C)
    (hgc : Continuous g) (hg : Integrable g volume) {D : ℝ} (hgb : ∀ x, |g x| ≤ D) (x : ℝ) :
    averageTranslate (μ ∗ ν) (functionConvolution f g) x =
      functionConvolution (averageTranslate μ f) (averageTranslate ν g) x := by
  rw [averageTranslate_conv μ ν (continuous_functionConvolution hfc hf hgc hgb)
    (abs_functionConvolution_le hf hgb)]
  have he : averageTranslate ν (functionConvolution f g) =
      functionConvolution f (averageTranslate ν g) :=
    funext (averageTranslate_functionConvolution_right ν hfc hf hgc hgb)
  rw [he]
  exact averageTranslate_functionConvolution_left μ
    (continuous_averageTranslate_of_bounded ν hgc hgb)
    (integrable_averageTranslate ν hgc hg) hfc hfb x

end LpSelfSimilar
