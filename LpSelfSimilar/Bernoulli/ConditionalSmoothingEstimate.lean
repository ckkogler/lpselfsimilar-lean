module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Bernoulli.ConditionalTailInversion
public import LpSelfSimilar.Fourier.NormalizedBlockConvolution
public import LpSelfSimilar.Analysis.ConditionalConvolutionBound

@[expose] public section

/-!
# Smoothing the actual conditional block decomposition

The original product label law, label-dependent translations, independent
unused-digit law and actual reserved infinite tail are retained. The norm
bound is for their actual measure convolution with the rescaled detail kernel.
Its analytic inputs are the already-proved mean bounds for normalized blocks;
the following packing application supplies those inputs from the criterion.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators

namespace LpSelfSimilar.Bernoulli

/-- The original conditional mixture with actual remainder and tail has the exact smoothing bound. -/
theorem conditional_blocks_smoothing_bound
    {m : ℕ} {Ω : Fin m → Type*} [∀ i, Fintype (Ω i)]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (p : (i : Fin m) → PMF (Ω i)) (μ : (i : Fin m) → Ω i → Measure ℝ)
    [∀ i a, IsProbabilityMeasure (μ i a)] (c : (i : Fin m) → Ω i → ℝ)
    (η : Measure ℝ) [IsProbabilityMeasure η]
    {θ ρ L r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (hr : 0 < r) (hrχ : r ≤ -Real.log θ)
    (T : ℕ) (hs : ∀ i a, ((μ i a).map (fun y ↦ (y - c i a) / r)) (Icc 0 52) = 1)
    (hb : ∀ ξ, |(|ξ| - 1)| ≤ packingFrequencyWidth (L / ρ) → ∀ j ≤ 2,
      (∫ ω, ‖iteratedDeriv j (charFun (finiteConvolution
        (fun i ↦ (μ i (ω i)).map (fun y ↦ (y - c i (ω i)) / r)))) ξ‖
          ∂(productPMF p).toMeasure) ≤
            (80 * L * T / (-Real.log θ)) ^ j *
              Real.exp (-(packingAttenuation (-Real.log θ) ρ L * T))) :
    (∫ x, ‖Analysis.measureFunctionConvolution
      ((pmfMixture (productPMF p) (fun ω ↦ finiteConvolution (fun i ↦ μ i (ω i))) ∗ η) ∗
        (convolution θ).map (fun y ↦ θ ^ reservedTailStart θ (packingFrequencyWidth (L / ρ)) r * y))
      (Analysis.rescaledKernel r (Fourier.angularInverseFourier
        (fun ξ ↦ (Fourier.quinticFourierDetail (packingFrequencyWidth (L / ρ)) ξ : ℂ)))) x‖) ≤
      smoothingPrefactor (-Real.log θ) (L / ρ) * ((T : ℝ) + 1) ^ 2 *
        Real.exp (-(packingAttenuation (-Real.log θ) ρ L) * T) := by
  let ε := packingFrequencyWidth (L / ρ)
  let τ := (convolution θ).map (fun y ↦ θ ^ reservedTailStart θ ε r * y)
  let S := fun ω : (i : Fin m) → Ω i ↦ finiteConvolution (fun i ↦ μ i (ω i))
  let μ' := fun i a ↦ (μ i a).map (fun y ↦ (y - c i a) / r)
  let F := fun ξ ↦ (Fourier.quinticFourierDetail ε ξ : ℂ)
  let K := Fourier.angularInverseFourier F
  have hε : 0 < ε := packingFrequencyWidth_pos
    (LpSelfSimilar.Entropy.three_le_separation_entropy_ratio hρ hρ1 hL)
  haveI : IsProbabilityMeasure τ := LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  haveI (ω : (i : Fin m) → Ω i) : IsProbabilityMeasure (S ω) := inferInstanceAs
    (IsProbabilityMeasure (finiteConvolution _))
  haveI (i : Fin m) (a : Ω i) : IsProbabilityMeasure (μ' i a) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  have hFi : Integrable F := (Fourier.integrable_quinticFourierDetail hε).ofReal
  have hKc : Continuous K := Fourier.continuous_angularInverseFourier hFi
  have hKi : Integrable K := (Fourier.integrable_continuous_angularInverseFourier_quinticDetail hε).1
  have hrc : Continuous (Analysis.rescaledKernel r K) := by
    unfold Analysis.rescaledKernel
    exact continuous_const.smul (hKc.comp (continuous_id.div_const r))
  have hri : Integrable (Analysis.rescaledKernel r K) := (hKi.comp_div hr.ne').smul _
  have hrb x : ‖Analysis.rescaledKernel r K x‖ ≤
      r⁻¹ * ((2 * Real.pi)⁻¹ * ∫ ξ, ‖F ξ‖) := by
    rw [Analysis.rescaledKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact mul_le_mul_of_nonneg_left (Fourier.norm_angularInverseFourier_le F (x / r)) (by positivity)
  have hmix := Analysis.integral_norm_mixture_remainder_tail_convolution_le
    (productPMF p) S η τ hrc hri hrb
  have hτ : τ.map (fun y ↦ y / r) =
      (convolution θ).map (fun y ↦ (θ ^ reservedTailStart θ ε r / r) * y) := by
    dsimp only [τ]
    rw [map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext y
    dsimp only [Function.comp_apply]
    ring
  have hnorm (ω : (i : Fin m) → Ω i) := Fourier.integral_norm_blocks_tail_eq_normalized_inverse
    (fun i ↦ μ i (ω i)) τ (fun i ↦ c i (ω i)) hε hr
  simp_rw [hτ] at hnorm
  have hbound := integral_inverse_normalized_blocks_reserved_tail_le p μ' hs
    hθ0 hθ1 hgap hρ hρ1 hL hr hrχ T hb
  calc
    _ ≤ ∫ ω, (∫ x, ‖Analysis.measureFunctionConvolution (S ω ∗ τ)
        (Analysis.rescaledKernel r K) x‖) ∂(productPMF p).toMeasure := hmix
    _ = ∫ ω, (∫ x, ‖Fourier.angularInverseFourier (Fourier.quinticDetailProduct ε
        (fun ξ ↦ charFun (finiteConvolution (fun i ↦ μ' i (ω i))) (-ξ) *
          charFun ((convolution θ).map (fun y ↦
            (θ ^ reservedTailStart θ ε r / r) * y)) (-ξ))) x‖) ∂(productPMF p).toMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ hnorm
    _ ≤ _ := hbound

end LpSelfSimilar.Bernoulli
