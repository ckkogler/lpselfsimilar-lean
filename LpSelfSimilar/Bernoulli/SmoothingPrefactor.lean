module

public import LpSelfSimilar.Fourier.QuinticMeanInversion
public import LpSelfSimilar.Bernoulli.PackingParameters

@[expose] public section

/-!
# The exact prefactor in the smoothing estimate

Substitution of the proved bandwidth and derivative cost gives the coefficient
`2 * 10^11` and the correction `0.001/(t*chi)`. These arithmetic estimates and
the finite-label inverse bound do not yet identify the inverse integral with
convolution of the full Bernoulli law; that identification is a separate step.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace LpSelfSimilar.Bernoulli

/-- The scale-independent coefficient in the quantitative smoothing estimate. -/
noncomputable def smoothingPrefactor (χ J : ℝ) : ℝ :=
  200000000000 * J ^ 2 * (packingLogScale J) ^ 2 *
    (1 + (1 / 1000) / (packingLogScale J * χ)) ^ 2 * Real.exp (-1 / (2 * χ))

/-- The smoothing prefactor is nonnegative without additional parameter hypotheses. -/
theorem smoothingPrefactor_nonneg (χ J : ℝ) : 0 ≤ smoothingPrefactor χ J := by
  unfold smoothingPrefactor
  positivity

/-- Exact rescaling before absorbing the additional constant term into T+1. -/
theorem smoothing_prefactor_substitution {J t χ T : ℝ}
    (hJ : 0 < J) (ht : 0 < t) (hχ : 0 < χ) (hT : 0 ≤ T) :
    20 / (1 / (100000 * J * t)) ^ 2 *
        (1 + (1 / (100000 * J * t)) * (100 * J * (T + 1) / χ)) ^ 2 ≤
      200000000000 * J ^ 2 * t ^ 2 * (T + 1) ^ 2 *
        (1 + (1 / 1000) / (t * χ)) ^ 2 := by
  have he : 20 / (1 / (100000 * J * t)) ^ 2 *
      (1 + (1 / (100000 * J * t)) * (100 * J * (T + 1) / χ)) ^ 2 =
      200000000000 * J ^ 2 * t ^ 2 * (1 + (T + 1) * ((1 / 1000) / (t * χ))) ^ 2 := by
    field_simp
    ring
  rw [he]
  have hz : 0 ≤ (1 / 1000 : ℝ) / (t * χ) := by positivity
  have hl : 0 ≤ 1 + (T + 1) * ((1 / 1000 : ℝ) / (t * χ)) := by positivity
  have hr : 0 ≤ (T + 1) * (1 + (1 / 1000 : ℝ) / (t * χ)) := by positivity
  have hb : 1 + (T + 1) * ((1 / 1000 : ℝ) / (t * χ)) ≤
      (T + 1) * (1 + (1 / 1000 : ℝ) / (t * χ)) := by nlinarith
  have hs : (1 + (T + 1) * ((1 / 1000 : ℝ) / (t * χ))) ^ 2 ≤
      ((T + 1) * (1 + (1 / 1000 : ℝ) / (t * χ))) ^ 2 := by nlinarith
  calc
    _ ≤ 200000000000 * J ^ 2 * t ^ 2 *
        ((T + 1) * (1 + (1 / 1000 : ℝ) / (t * χ))) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- The actual finite-label inverse integral has the exact coefficient used in (5.4). -/
theorem integral_quinticDetail_inverse_le_smoothingPrefactor
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : PMF ι) (P : ι → ℝ → ℂ) {χ J a : ℝ} (hχ : 0 < χ) (hJ : 3 ≤ J)
    (T : ℕ) (hP : ∀ i, ContDiff ℝ 2 (P i))
    (hb : ∀ ξ, |(|ξ| - 1)| ≤ packingFrequencyWidth J → ∀ j ≤ 2,
      (∫ i, ‖iteratedDeriv j (P i) ξ‖ ∂p.toMeasure) ≤
        (100 * J * ((T : ℝ) + 1) / χ) ^ j *
          (Real.exp (-1 / (2 * χ)) * Real.exp (-a * T))) :
    (∫ i, (∫ x, ‖Fourier.angularInverseFourier
        (Fourier.quinticDetailProduct (packingFrequencyWidth J) (P i)) x‖) ∂p.toMeasure) ≤
      smoothingPrefactor χ J * ((T : ℝ) + 1) ^ 2 * Real.exp (-a * T) := by
  have hJpos : 0 < J := by linarith
  have ht : 0 < packingLogScale J := lt_trans (by norm_num) (six_lt_packingLogScale hJ)
  have h := Fourier.integral_quinticDetail_inverse_L1_le_twenty p P
    (packingFrequencyWidth_pos hJ) (packingFrequencyWidth_lt hJ).le
    (by positivity) (by positivity) hP hb
  have hc := smoothing_prefactor_substitution hJpos ht hχ (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
  change 20 / (packingFrequencyWidth J) ^ 2 *
      (1 + packingFrequencyWidth J * (100 * J * ((T : ℝ) + 1) / χ)) ^ 2 ≤ _ at hc
  calc
    _ ≤ _ := h
    _ ≤ (200000000000 * J ^ 2 * (packingLogScale J) ^ 2 * ((T : ℝ) + 1) ^ 2 *
        (1 + (1 / 1000) / (packingLogScale J * χ)) ^ 2) *
          (Real.exp (-1 / (2 * χ)) * Real.exp (-a * T)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by unfold smoothingPrefactor; ring

end LpSelfSimilar.Bernoulli
