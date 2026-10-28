module

public import LpSelfSimilar.Bernoulli.PackingSmoothingEstimate
public import LpSelfSimilar.Bernoulli.ReservedTailSmoothing

@[expose] public section

/-!
# The full quantitative detail smoothing estimate

The number of retained length families is zero below the packing threshold and
the exact logarithmic count above it. Both cases concern convolution of the
actual Bernoulli measure with the same explicitly rescaled detail kernel.
-/

open MeasureTheory
open LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The source's length-family count, including the tail-only range. -/
noncomputable def smoothingLengthCount (χ ρ L R : ℝ) : ℕ :=
  if packingScaleThreshold χ ρ L ≤ R then packingLengthCount χ ρ L R else 0

/-- Below the threshold the actual smoothing construction uses only the reserved tail. -/
theorem smoothingLengthCount_of_lt {χ ρ L R : ℝ} (hR : R < packingScaleThreshold χ ρ L) :
    smoothingLengthCount χ ρ L R = 0 := by
  simp only [smoothingLengthCount, if_neg (not_le.mpr hR)]

/-- At and above the threshold the exact previously constructed packing count is used. -/
theorem smoothingLengthCount_of_le {χ ρ L R : ℝ} (hR : packingScaleThreshold χ ρ L ≤ R) :
    smoothingLengthCount χ ρ L R = packingLengthCount χ ρ L R := by
  simp only [smoothingLengthCount, if_pos hR]

/-- The full (5.4) bound for the actual Bernoulli law, including the tail-only range. -/
theorem bernoulli_detail_smoothing_bound {θ ρ L R : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (hrχ : (2 : ℝ) ^ (-R) ≤ -Real.log θ)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let T := smoothingLengthCount (-Real.log θ) ρ L R
    (∫ x, ‖Analysis.measureFunctionConvolution (convolution θ)
      (Analysis.rescaledKernel ((2 : ℝ) ^ (-R)) (Fourier.angularInverseFourier
        (fun ξ ↦ (Fourier.quinticFourierDetail (packingFrequencyWidth (L / ρ)) ξ : ℂ)))) x‖) ≤
      smoothingPrefactor (-Real.log θ) (L / ρ) * ((T : ℝ) + 1) ^ 2 *
        Real.exp (-(packingAttenuation (-Real.log θ) ρ L) * T) := by
  dsimp only
  by_cases hR : packingScaleThreshold (-Real.log θ) ρ L ≤ R
  · rw [smoothingLengthCount_of_le hR]
    exact packing_smoothing_bound hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hR hentropy hsep
  · rw [smoothingLengthCount_of_lt (lt_of_not_ge hR)]
    simpa only [Nat.cast_zero, zero_add, one_pow, mul_one, mul_zero, Real.exp_zero] using
      reserved_tail_smoothing_bound hθ0 hθ1 hgap hρ hρ1 hL
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-R)) hrχ

end LpSelfSimilar.Bernoulli
