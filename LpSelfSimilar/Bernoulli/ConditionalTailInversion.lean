module

public import LpSelfSimilar.Bernoulli.SmoothingPrefactor
public import LpSelfSimilar.Bernoulli.ReservedTailProductDerivatives
public import LpSelfSimilar.Fourier.ReflectedCharacteristicProducts

@[expose] public section

/-!
# Inversion for actual normalized blocks and the reserved tail

The amplitudes are characteristic functions of the actual conditional block
laws and the actual reserved Bernoulli tail. Their C2 smoothness follows from
bounded moments. The reflected frequency is retained so that the resulting
inverse integral has the convention needed for actual measure convolution.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LpSelfSimilar.Bernoulli

/-- Actual normalized conditional blocks and reserved tail obey the full inverse prefactor bound. -/
theorem integral_inverse_normalized_blocks_reserved_tail_le
    {m : ℕ} {Ω : Fin m → Type*} [∀ i, Fintype (Ω i)]
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (p : (i : Fin m) → PMF (Ω i)) (μ : (i : Fin m) → Ω i → Measure ℝ)
    [∀ i a, IsProbabilityMeasure (μ i a)] (hs : ∀ i a, μ i a (Icc 0 52) = 1)
    {θ ρ L r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (hr : 0 < r) (hrχ : r ≤ -Real.log θ)
    (T : ℕ)
    (hb : ∀ ξ, |(|ξ| - 1)| ≤ packingFrequencyWidth (L / ρ) → ∀ j ≤ 2,
      (∫ ω, ‖iteratedDeriv j (charFun (finiteConvolution (fun i ↦ μ i (ω i)))) ξ‖
        ∂(productPMF p).toMeasure) ≤
          (80 * L * T / (-Real.log θ)) ^ j *
            Real.exp (-(packingAttenuation (-Real.log θ) ρ L * T))) :
    (∫ ω, (∫ x, ‖Fourier.angularInverseFourier
      (Fourier.quinticDetailProduct (packingFrequencyWidth (L / ρ))
        (fun ξ ↦ charFun (finiteConvolution (fun i ↦ μ i (ω i))) (-ξ) *
          charFun ((convolution θ).map (fun y ↦
            (θ ^ reservedTailStart θ (packingFrequencyWidth (L / ρ)) r / r) * y)) (-ξ))) x‖)
        ∂(productPMF p).toMeasure) ≤
      smoothingPrefactor (-Real.log θ) (L / ρ) * ((T : ℝ) + 1) ^ 2 *
        Real.exp (-(packingAttenuation (-Real.log θ) ρ L) * T) := by
  let f := fun ω : (i : Fin m) → Ω i ↦ charFun (finiteConvolution (fun i ↦ μ i (ω i)))
  let a := θ ^ reservedTailStart θ (packingFrequencyWidth (L / ρ)) r / r
  let g := charFun ((convolution θ).map (fun y ↦ a * y))
  let P := fun ω ξ ↦ f ω ξ * g ξ
  have hf (ω : (i : Fin m) → Ω i) : ContDiff ℝ 2 (f ω) :=
    Fourier.contDiff_charFun_finiteConvolution_of_ae_abs_le (fun i ↦ μ i (ω i)) (fun _ ↦ 52)
      (fun i ↦ Fourier.ae_abs_le_of_mass_Icc_eq_one (μ i (ω i)) (hs i (ω i))) 2
  have hg : ContDiff ℝ 2 g := contDiff_charFun (memLp_id_scaled_convolution hθ0.le hθ1 a 2)
  have hP ω : ContDiff ℝ 2 (P ω) := (hf ω).mul hg
  have hmean ξ (hξ : |(|ξ| - 1)| ≤ packingFrequencyWidth (L / ρ)) (j : ℕ) (hj : j ≤ 2) :
      (∫ ω, ‖iteratedDeriv j (P ω) ξ‖ ∂(productPMF p).toMeasure) ≤
        (100 * (L / ρ) * ((T : ℝ) + 1) / (-Real.log θ)) ^ j *
          (Real.exp (-1 / (2 * (-Real.log θ))) *
            Real.exp (-(packingAttenuation (-Real.log θ) ρ L) * T)) := by
    have h := integral_norm_iteratedDeriv_mul_reserved_tail_le (productPMF p) f
      hθ0 hθ1 hgap hρ hρ1 hL hr hrχ T ξ hξ
      (fun ω ↦ (hf ω).contDiffAt) (hb ξ hξ) j hj
    simpa only [P, g, a, mul_assoc, neg_mul] using h
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  apply integral_quinticDetail_inverse_le_smoothingPrefactor (productPMF p)
    (fun ω ξ ↦ P ω (-ξ)) hχ
    (LpSelfSimilar.Entropy.three_le_separation_entropy_ratio hρ hρ1 hL) T
    (fun ω ↦ (hP ω).comp contDiff_neg)
  exact Fourier.integral_norm_iteratedDeriv_reflect_band_le
    (productPMF p).toMeasure P 2 hmean

end LpSelfSimilar.Bernoulli
