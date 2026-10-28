module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Probability.AffineConvolution
public import LpSelfSimilar.Analysis.AffineKernelConvolution
public import LpSelfSimilar.Fourier.AngularMeasureConvolution
public import LpSelfSimilar.Fourier.QuinticDetailKernel

@[expose] public section

/-!
# Actual block convolution and its normalized inverse integral

Each block may have a different translation. Their translations add, and their
common rescaling combines with the normalized reserved tail. The exact affine
kernel identity cancels that total translation and rescaling from the L1 norm.
-/

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace LpSelfSimilar.Fourier

/-- The actual conditional block/tail convolution has the normalized product's inverse norm. -/
theorem integral_norm_blocks_tail_eq_normalized_inverse {m : ℕ}
    (μ : Fin m → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (τ : Measure ℝ) [IsProbabilityMeasure τ] (c : Fin m → ℝ)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    (∫ x, ‖Analysis.measureFunctionConvolution (finiteConvolution μ ∗ τ)
      (Analysis.rescaledKernel r (angularInverseFourier (fun ξ ↦ (quinticFourierDetail ε ξ : ℂ)))) x‖) =
      ∫ x, ‖angularInverseFourier (quinticDetailProduct ε
        (fun ξ ↦ charFun (finiteConvolution (fun i ↦ (μ i).map (fun y ↦ (y - c i) / r))) (-ξ) *
          charFun (τ.map (fun y ↦ y / r)) (-ξ))) x‖ := by
  let β := finiteConvolution (fun i ↦ (μ i).map (fun y ↦ (y - c i) / r)) ∗
    τ.map (fun y ↦ y / r)
  haveI (i : Fin m) : IsProbabilityMeasure ((μ i).map (fun y ↦ (y - c i) / r)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure (τ.map (fun y ↦ y / r)) := LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  haveI : IsProbabilityMeasure β := inferInstanceAs (IsProbabilityMeasure (_ ∗ _))
  have hβ : β = (finiteConvolution μ ∗ τ).map (fun y ↦ (y - ∑ i, c i) / r) := by
    dsimp only [β]
    rw [finiteConvolution_map_sub_div, conv_map_sub_div_map_div]
  have he : β.map (fun y ↦ r * y + ∑ i, c i) = finiteConvolution μ ∗ τ := by
    rw [hβ]
    exact map_sub_div_inverse _ _ hr.ne'
  have hi : Integrable (fun ξ ↦ (quinticFourierDetail ε ξ : ℂ)) :=
    (integrable_quinticFourierDetail hε).ofReal
  have hc := continuous_angularInverseFourier hi
  rw [← he, Analysis.integral_norm_measureFunctionConvolution_map_affine_rescaled β hc _ hr]
  have hid x := measureFunctionConvolution_angularInverseFourier β hi x
  simp_rw [hid]
  have hf : (fun ξ ↦ (quinticFourierDetail ε ξ : ℂ) * charFun β (-ξ)) =
      quinticDetailProduct ε (fun ξ ↦
        charFun (finiteConvolution (fun i ↦ (μ i).map (fun y ↦ (y - c i) / r))) (-ξ) *
          charFun (τ.map (fun y ↦ y / r)) (-ξ)) := by
    funext ξ
    dsimp only [β, quinticDetailProduct]
    rw [charFun_conv]
  rw [hf]

end LpSelfSimilar.Fourier
