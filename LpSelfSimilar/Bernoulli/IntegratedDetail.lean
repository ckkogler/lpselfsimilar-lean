module

public import LpSelfSimilar.Bernoulli.IntegratedLogarithmicDetail
public import LpSelfSimilar.Bernoulli.PackingThresholdUpperBound
public import LpSelfSimilar.Analysis.LogarithmicHalfLineIntegral

@[expose] public section

/-!
# The integrated Bernoulli detail estimate

The actual logarithmic detail integral is transferred to spatial scale by the
proved Jacobian identity. Its upper scale is the logarithmic gap chi, and the
factor log(2) is at most one. This proves (5.5), including integrability at zero,
then substitutes the rounded threshold to obtain the exact coefficient (5.6).
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Full scale-integrated detail estimate (5.5) for the actual Bernoulli convolution. -/
theorem bernoulli_integrated_detail_bound {θ ρ L : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let ψ := Fourier.angularInverseFourier
      (fun ξ ↦ (Fourier.quinticFourierDetail (packingFrequencyWidth (L / ρ)) ξ : ℂ))
    let d := fun r : ℝ => ∫ x, ‖measureFunctionConvolution (convolution θ) (rescaledKernel r ψ) x‖
    IntegrableOn (fun r => d r / r) (Ioc 0 (-Real.log θ)) volume ∧
      (∫ r in Ioc 0 (-Real.log θ), d r / r) ≤
        2 * smoothingPrefactor (-Real.log θ) (L / ρ) * packingScaleThreshold (-Real.log θ) ρ L := by
  let χ := -Real.log θ
  let a := -Real.log χ / Real.log 2
  have hχ : 0 < χ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hχ1 : χ ≤ 1 := by dsimp [χ]; linarith
  have hk : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 ≤ a := div_nonneg (neg_nonneg.mpr (Real.log_nonpos hχ.le hχ1)) hk.le
  have he : Real.exp (-Real.log 2 * a) = χ := by
    have hx : -Real.log 2 * a = Real.log χ := by dsimp [a]; field_simp
    rw [hx, Real.exp_log hχ]
  have hdyadic (R : ℝ) : (2 : ℝ) ^ (-R) = Real.exp (-Real.log 2 * R) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  have hr : (2 : ℝ) ^ (-a) ≤ -Real.log θ := by rw [hdyadic, he]
  have hlog := bernoulli_detail_logarithmic_integral_bound
    hθ0 hθ1 hgap hρ hρ1 hL hC hsmall ha hr hentropy hsep
  dsimp only at hlog ⊢
  let f : ℝ → ℝ := fun r => ∫ x, ‖measureFunctionConvolution (convolution θ)
    (rescaledKernel r (Fourier.angularInverseFourier
      (fun ξ ↦ (Fourier.quinticFourierDetail (packingFrequencyWidth (L / ρ)) ξ : ℂ)))) x‖
  change IntegrableOn (fun R => f ((2 : ℝ) ^ (-R))) (Ici a) volume ∧
    (∫ R in Ici a, f ((2 : ℝ) ^ (-R))) ≤
      2 * smoothingPrefactor χ (L / ρ) * packingScaleThreshold χ ρ L at hlog
  simp_rw [hdyadic] at hlog
  change IntegrableOn (fun r => f r / r) (Ioc 0 χ) volume ∧
    (∫ r in Ioc 0 χ, f r / r) ≤
      2 * smoothingPrefactor χ (L / ρ) * packingScaleThreshold χ ρ L
  have hi := (integrableOn_div_iff_exp_neg_mul f hk a).mpr hlog.1
  rw [he] at hi
  refine ⟨hi, ?_⟩
  have heq := integral_div_eq_mul_integral_exp_neg_mul f hk a
  rw [he] at heq
  calc
    _ = Real.log 2 * ∫ R in Ici a, f (Real.exp (-Real.log 2 * R)) := heq
    _ ≤ Real.log 2 * (2 * smoothingPrefactor χ (L / ρ) * packingScaleThreshold χ ρ L) :=
      mul_le_mul_of_nonneg_left hlog.2 hk.le
    _ ≤ 2 * smoothingPrefactor χ (L / ρ) * packingScaleThreshold χ ρ L := by
      have hB := smoothingPrefactor_nonneg χ (L / ρ)
      have hA := packingScaleThreshold_pos hχ hρ hρ1 hL
      have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      exact mul_le_of_le_one_left (by positivity) hlog2

/-- The integrated estimate divided by the gap has the exact coefficient in (5.6). -/
theorem bernoulli_integrated_detail_div_gap_bound {θ ρ L : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let χ := -Real.log θ
    let ψ := Fourier.angularInverseFourier
      (fun ξ ↦ (Fourier.quinticFourierDetail (packingFrequencyWidth (L / ρ)) ξ : ℂ))
    ((∫ r in Ioc 0 χ,
      (∫ x, ‖measureFunctionConvolution (convolution θ) (rescaledKernel r ψ) x‖) / r) / χ) ≤
      2400000000000000000 * (L / ρ) ^ 4 * packingLogScale (L / ρ) ^ 3 / χ ^ 2 *
        (1 + (1 / 1000 : ℝ) / (packingLogScale (L / ρ) * χ)) ^ 2 *
        Real.exp (-1 / (2 * χ)) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  exact (div_le_div_of_nonneg_right
    (bernoulli_integrated_detail_bound hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hentropy hsep).2 hχ.le).trans
    (smoothingPrefactor_mul_threshold_div_gap_le hχ (by linarith) hρ hρ1 hL)

end LpSelfSimilar.Bernoulli
