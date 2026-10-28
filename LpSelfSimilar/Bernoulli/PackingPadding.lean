module

public import LpSelfSimilar.Bernoulli.PackingParameters

@[expose] public section

/-!
# Phase padding and endpoint losses at the starting block length

The ceiling defining the first length absorbs the finite phase range and the
fixed entropy endpoint errors. The bounds retain the source's factors of one
million, ten, and `52*epsilon`, including their strict numerical margins.
-/

open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The phase padding ratio obeys its explicit bound and is below one millionth. -/
theorem packing_phase_padding_ratio_bounds {θ J : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hJ : 3 ≤ J) (n : ℕ)
    (hn : packingBaseLength (-Real.log θ) J ≤ n) :
    ((geometricPhaseLength θ : ℝ) + 2) / n ≤
        (Real.log 10000 + 3 * (-Real.log θ)) / (1000000 * J * packingLogScale J) ∧
      (Real.log 10000 + 3 * (-Real.log θ)) / (1000000 * J * packingLogScale J) <
        (1 / 1000000 : ℝ) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have ht := six_lt_packingLogScale hJ
  have hbase : 1000000 * J * packingLogScale J / (-Real.log θ) ≤ (n : ℝ) :=
    (packingBaseLength_lower_bound _ _).trans (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hbase
  have hK : (geometricPhaseLength θ : ℝ) < Real.log 10000 / (-Real.log θ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hnum : 0 < Real.log 10000 + 3 * (-Real.log θ) := by positivity
  have hKχ := mul_lt_mul_of_pos_right hK hχ
  rw [add_mul, div_mul_cancel₀ _ hχ.ne', one_mul] at hKχ
  constructor
  · calc
      _ ≤ ((Real.log 10000 + 3 * (-Real.log θ)) / (-Real.log θ)) / n := by
        apply div_le_div_of_nonneg_right _ hn0.le
        apply (le_div_iff₀ hχ).mpr
        linarith
      _ ≤ ((Real.log 10000 + 3 * (-Real.log θ)) / (-Real.log θ)) /
          (1000000 * J * packingLogScale J / (-Real.log θ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hbase
      _ = _ := by field_simp [(Real.log_neg hθ0 hθ1).ne]
  · apply (div_lt_iff₀ (by positivity : 0 < 1000000 * J * packingLogScale J)).mpr
    nlinarith [log_ten_thousand_lt_ten]

/-- The width contribution to the main integral budget has its exact entropy-normalized value. -/
theorem packing_frequency_width_mul_length {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 < L) :
    52 * packingFrequencyWidth (L / ρ) * L =
      (13 / 25000 : ℝ) * ρ / packingLogScale (L / ρ) := by
  unfold packingFrequencyWidth
  field_simp
  <;> ring

/-- The initial length makes the fixed endpoint loss at most the stated gap-dependent error. -/
theorem packing_endpoint_loss_le {χ ρ L : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (n : ℕ) (hn : packingBaseLength χ (L / ρ) ≤ n) :
    10 * L / n ≤ (1 / 100000 : ℝ) * ρ * χ / packingLogScale (L / ρ) := by
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have ht := six_lt_packingLogScale hJ
  have hbase : 1000000 * (L / ρ) * packingLogScale (L / ρ) / χ ≤ (n : ℝ) :=
    (packingBaseLength_lower_bound _ _).trans (by exact_mod_cast hn)
  calc
    _ ≤ 10 * L / (1000000 * (L / ρ) * packingLogScale (L / ρ) / χ) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hbase
    _ = _ := by field_simp; ring

/-- The endpoint loss is strictly below one millionth of the entropy-to-log-scale ratio. -/
theorem packing_endpoint_loss_lt {χ ρ L : ℝ} (hχ : 0 < χ) (hχ1 : χ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (n : ℕ)
    (hn : packingBaseLength χ (L / ρ) ≤ n) :
    10 * L / n < (1 / 1000000 : ℝ) * ρ / packingLogScale (L / ρ) := by
  have ht : 0 < packingLogScale (L / ρ) := by
    linarith [six_lt_packingLogScale (three_le_separation_entropy_ratio hρ hρ1 hL)]
  apply lt_of_le_of_lt (packing_endpoint_loss_le hχ hρ hρ1 hL n hn)
  apply div_lt_div_of_pos_right _ ht
  nlinarith

end LpSelfSimilar.Bernoulli
