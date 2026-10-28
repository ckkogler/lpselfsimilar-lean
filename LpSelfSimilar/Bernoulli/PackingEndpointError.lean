module

public import LpSelfSimilar.Bernoulli.PackingParameters

@[expose] public section

/-!
# Absorbing the finite entropy endpoint error

The exact endpoint term from the integrated cancellation budget, together with
the `208*epsilon` frequency correction, is strictly below `10*L`. The only
extra numerical input is the working criterion's explicit logarithmic gap bound.
-/

open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The entropy-to-cancellation slope is at least one throughout the admissible range. -/
theorem packing_cancellationSlope_one_le {J : ℝ} (hJ : 3 ≤ J) :
    1 ≤ cancellationSlope J := by
  have ht := six_lt_packingLogScale hJ
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold cancellationSlope
  apply (le_div_iff₀ (by positivity : 0 < (13 / 40 : ℝ) * Real.log 2)).mpr
  change 6 < Real.log (150 * J) at ht
  nlinarith [Real.log_two_lt_d9]

/-- The entropy remainder is at most one, a sufficient bound for the endpoint budget. -/
theorem packing_cancellationRemainder_le_one {J : ℝ} (hJ : 3 ≤ J) :
    cancellationRemainder J ≤ 1 := by
  have hl : (69 / 100 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  apply (cancellationRemainder_le (by linarith : 0 < J)).trans
  apply (div_le_iff₀ (by positivity : 0 < 10 * J * Real.log 2)).mpr
  nlinarith

/-- The complete entropy endpoint and frequency correction fit strictly inside `10*L`. -/
theorem packing_entropy_endpoint_error_lt (θ : ℝ) {ρ L : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2) :
    (4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) +
        4 * cancellationRemainder (L / ρ)) / cancellationSlope (L / ρ) +
      208 * packingFrequencyWidth (L / ρ) < 10 * L := by
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have hα := packing_cancellationSlope_one_le hJ
  have hβ := packing_cancellationRemainder_le_one hJ
  have he := packingFrequencyWidth_lt hJ
  have hnum : 4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) +
      4 * cancellationRemainder (L / ρ) ≤ 4 * L + 12 := by linarith
  have hquot : (4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) +
      4 * cancellationRemainder (L / ρ)) / cancellationSlope (L / ρ) ≤ 4 * L + 12 := by
    calc
      _ ≤ (4 * L + 12) / cancellationSlope (L / ρ) :=
        div_le_div_of_nonneg_right hnum (by linarith)
      _ ≤ (4 * L + 12) / 1 :=
        div_le_div_of_nonneg_left (by positivity) zero_lt_one hα
      _ = _ := div_one _
  linarith

end LpSelfSimilar.Bernoulli
