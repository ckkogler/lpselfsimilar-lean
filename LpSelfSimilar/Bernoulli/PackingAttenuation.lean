module

public import LpSelfSimilar.Bernoulli.PackingParameters

@[expose] public section

/-!
# Attenuation outweighs the cost of changing block length

The exact `0.50093` margin in the integrated cancellation budget implies
`a_* > t` under the working criterion's quadratic smallness assumption.
The rounded length multiplier therefore satisfies `N*exp(-a_*) <= 1/15`.
-/

open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Exact strict lower bound for the attenuation of one complete block-length family. -/
theorem packingAttenuation_lower_bound {χ ρ L : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) :
    (50093 / 100000 : ℝ) * ρ / (χ * packingLogScale (L / ρ)) < packingAttenuation χ ρ L := by
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have ht : 0 < packingLogScale (L / ρ) := by linarith [six_lt_packingLogScale hJ]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hW := bandCancellationRate_lower_bound hρ hρ1 hL
  have hcoef : 0 ≤ (999 / 1000 : ℝ) / (χ / Real.log 2) := by positivity
  calc
    _ < ((999 / 1000 : ℝ) * ((13 / 40 : ℝ) * (Real.log 2) ^ 2 *
          (84 / 25 - 1 / (10 * Real.log 2)) - (1 / 1000 : ℝ) * Real.log 2)) *
          ρ / (χ * packingLogScale (L / ρ)) :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_right packing_cancellation_margin_gt hρ)
        (mul_pos hχ ht)
    _ = (999 / 1000 : ℝ) / (χ / Real.log 2) *
        (((13 / 40 : ℝ) * ρ * Real.log 2 / packingLogScale (L / ρ)) *
          (84 / 25 - 1 / (10 * Real.log 2)) - ρ / (1000 * packingLogScale (L / ρ))) := by
      field_simp
      <;> ring
    _ ≤ packingAttenuation χ ρ L :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right hW _) hcoef

/-- The working criterion makes the attenuation strictly exceed its logarithmic length cost. -/
theorem packingLogScale_lt_attenuation {χ ρ L : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : χ * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2) :
    packingLogScale (L / ρ) < packingAttenuation χ ρ L := by
  have ht : 0 < packingLogScale (L / ρ) := by
    linarith [six_lt_packingLogScale (three_le_separation_entropy_ratio hρ hρ1 hL)]
  apply lt_trans ?_ (packingAttenuation_lower_bound hχ hρ hρ1 hL)
  apply (lt_div_iff₀ (mul_pos hχ ht)).mpr
  nlinarith

/-- The exact rounded length multiplier and attenuation give a summability ratio at most `1/15`. -/
theorem packingLengthMultiplier_mul_exp_neg_attenuation_le {χ ρ L : ℝ}
    (hχ : 0 < χ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : χ * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2) :
    (packingLengthMultiplier (L / ρ) : ℝ) * Real.exp (-packingAttenuation χ ρ L) ≤
      (1 / 15 : ℝ) := by
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have ha := packingLogScale_lt_attenuation hχ hρ hρ1 hL hsmall
  have hN := (packingLengthMultiplier_bounds hJ).2
  calc
    _ ≤ (10 * (L / ρ)) * Real.exp (-packingAttenuation χ ρ L) :=
      mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
    _ ≤ (10 * (L / ρ)) * Real.exp (-packingLogScale (L / ρ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    _ = (1 / 15 : ℝ) := by
      rw [packingLogScale, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
      <;> ring

end LpSelfSimilar.Bernoulli
