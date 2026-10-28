module

public import LpSelfSimilar.Analysis.GeometricCountIntegration
public import LpSelfSimilar.Analysis.MeasurableKernelConvolution
public import LpSelfSimilar.Bernoulli.SmoothingCountBounds
public import LpSelfSimilar.Bernoulli.PackingAttenuation

@[expose] public section

/-!
# Integrability of the actual Bernoulli detail on logarithmic scales

The full smoothing estimate is summed over the measurable fibers of the actual
length count. Their upper endpoints and the attenuation ratio are proved from
the packing parameters. No integrability or density assumption is added.
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The actual detail is integrable over every admissible logarithmic half-line, with the exact bound. -/
theorem bernoulli_detail_logarithmic_integral_bound {θ ρ L R₁ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (hR₁ : 0 ≤ R₁) (hrχ : (2 : ℝ) ^ (-R₁) ≤ -Real.log θ)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let ψ := Fourier.angularInverseFourier
      (fun ξ ↦ (Fourier.quinticFourierDetail (packingFrequencyWidth (L / ρ)) ξ : ℂ))
    let d := fun R : ℝ => ∫ x, ‖measureFunctionConvolution (convolution θ)
      (rescaledKernel ((2 : ℝ) ^ (-R)) ψ) x‖
    IntegrableOn d (Ici R₁) volume ∧ (∫ R in Ici R₁, d R) ≤
      2 * smoothingPrefactor (-Real.log θ) (L / ρ) * packingScaleThreshold (-Real.log θ) ρ L := by
  dsimp only
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have hN := twenty_seven_le_packingLengthMultiplier hJ
  have hNpos : (0 : ℝ) < packingLengthMultiplier (L / ρ) := by
    exact_mod_cast (show 0 < packingLengthMultiplier (L / ρ) by omega)
  have hkernel := (Fourier.integrable_continuous_angularInverseFourier_quinticDetail
    (packingFrequencyWidth_pos hJ)).2
  apply integrableOn_and_integral_le_of_geometric_count
    (packingScaleThreshold_pos hχ hρ hρ1 hL) hNpos
    (smoothingPrefactor_nonneg _ _) hR₁ (measurable_smoothingLengthCount _ _ _)
  · exact (measurable_integral_norm_measureFunctionConvolution_rescaled
      (convolution θ) hkernel.measurable).comp (by fun_prop)
  · intro R
    exact integral_nonneg (fun x => norm_nonneg _)
  · intro R _
    exact lt_threshold_mul_pow_smoothingLengthCount hχ hρ hρ1 hL R
  · intro R hR
    have hr : (2 : ℝ) ^ (-R) ≤ -Real.log θ :=
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg hR)).trans hrχ
    exact bernoulli_detail_smoothing_bound hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hr hentropy hsep
  · exact packingLengthMultiplier_mul_exp_neg_attenuation_le hχ hρ hρ1 hL hsmall

end LpSelfSimilar.Bernoulli
