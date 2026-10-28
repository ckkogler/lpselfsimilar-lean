module

public import LpSelfSimilar.Bernoulli.ConditionalSmoothingEstimate
public import LpSelfSimilar.Bernoulli.PackingDerivativeBounds
public import LpSelfSimilar.Bernoulli.ReservedBandMixture
public import LpSelfSimilar.Bernoulli.PackingSmoothingRange

@[expose] public section

/-!
# The actual smoothing estimate from the constructed digit packing

Every conditional block and translation comes from the verified multiscale
packing. The scale bound and the endpoint separation from the reserved tail
are derived. Thus the estimate for the actual Bernoulli convolution has only
the working criterion's numerical and finite entropy/separation hypotheses.
-/

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators
open LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Equation (5.4) at every logarithmic scale admitting the full constructed packing. -/
theorem packing_smoothing_bound {θ ρ L R : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (hR : packingScaleThreshold (-Real.log θ) ρ L ≤ R)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let T := packingLengthCount (-Real.log θ) ρ L R
    (∫ x, ‖Analysis.measureFunctionConvolution (convolution θ)
      (Analysis.rescaledKernel ((2 : ℝ) ^ (-R)) (Fourier.angularInverseFourier
        (fun ξ ↦ (Fourier.quinticFourierDetail (packingFrequencyWidth (L / ρ)) ξ : ℂ)))) x‖) ≤
      smoothingPrefactor (-Real.log θ) (L / ρ) * ((T : ℝ) + 1) ^ 2 *
        Real.exp (-(packingAttenuation (-Real.log θ) ρ L) * T) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  let r := (2 : ℝ) ^ (-R)
  let ε := packingFrequencyWidth (L / ρ)
  let tail := reservedTailStart θ ε r
  let T := packingLengthCount (-Real.log θ) ρ L R
  have hr : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hrχ : r ≤ -Real.log θ := dyadic_scale_le_gap_of_packing_threshold hχ hρ hρ1 hL hR
  obtain ⟨m, scale, j, start, η₀, c, hcount, hb, hscale, hd, hcoord, hbudget, hs, hη₀, heq₀, hmean⟩ :=
    exists_packing_normalized_derivative_bounds hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hR hentropy hsep
  let len := fun i : Fin m ↦ packingBlockLength (-Real.log θ) (L / ρ) (scale i)
  have hlen i : 0 < len i := packingBlockLength_pos hχ hJ (scale i)
  have htcoord : R - (-Real.log θ / Real.log 2) * tail < 2 :=
    reservedTailStart_coordinate_lt_two hθ0 hθ1 hgap
      (packingFrequencyWidth_pos hJ).le (packingFrequencyWidth_lt hJ).le hrχ
  have hend i : start i + len i ≤ tail :=
    block_endpoint_le_of_coordinate_cutoff
      (div_nonneg hχ.le (Real.log_pos (by norm_num)).le)
      (start i) (len i) tail (hlen i) (hcoord i) htcoord.le
  obtain ⟨η, hη, heq⟩ := convolution_eq_disjoint_band_mixture_before
    (show |θ| < 1 by rwa [abs_of_pos hθ0]) start len j tail hend hd
  haveI : IsProbabilityMeasure η := hη
  have h := conditional_blocks_smoothing_bound
    (fun i ↦ digitBandLabelPMF θ (len i) (j i))
    (fun i ↦ digitBandShiftedLaw θ (len i) (j i) (start i : ℤ)) c η
    hθ0 hθ1 hgap hρ hρ1 hL hr hrχ T hs hmean
  rw [← heq] at h
  exact h

end LpSelfSimilar.Bernoulli
