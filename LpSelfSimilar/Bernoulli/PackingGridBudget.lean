module

public import LpSelfSimilar.Bernoulli.PackingAttenuation
public import LpSelfSimilar.Bernoulli.PackingPadding
public import LpSelfSimilar.Bernoulli.PackingEndpointError
public import LpSelfSimilar.Bernoulli.PackingGridCount

@[expose] public section

/-!
# Exact attenuation budget for one block length

The main rate survives the frequency loss, endpoint error and finite phase
padding. This proves the numerical inequality underlying the finite grid
selection, with the target attenuation defined by the exact factor `0.999`.
-/

open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Frequency loss and padding leave at least the required attenuation at each admissible length. -/
theorem packing_grid_attenuation_budget {θ ρ L : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (n : ℕ) (hn : packingBaseLength (-Real.log θ) (L / ρ) ≤ n) :
    packingAttenuation (-Real.log θ) ρ L ≤
      (n * (bandCancellationRate ρ L - 52 * packingFrequencyWidth (L / ρ) * L) - 10 * L) /
        packingGridSpacing (-Real.log θ) n (geometricPhaseLength θ) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have ht : 0 < packingLogScale (L / ρ) := by linarith [six_lt_packingLogScale hJ]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : 1000000 * (L / ρ) * packingLogScale (L / ρ) / (-Real.log θ) ≤ (n : ℝ) :=
    (packingBaseLength_lower_bound _ _).trans (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hbase
  have hpad := packing_phase_padding_ratio_bounds hθ0 hθ1 hgap hJ n hn
  have hp := (div_lt_iff₀ hn0).mp (hpad.1.trans_lt hpad.2)
  have hpadded : (999 / 1000 : ℝ) * ((n : ℝ) + geometricPhaseLength θ + 2) ≤ n := by
    nlinarith
  have ha0 : 0 < packingAttenuation (-Real.log θ) ρ L :=
    lt_trans (by positivity) (packingAttenuation_lower_bound hχ hρ hρ1 hL)
  have hδ : 0 < bandCancellationRate ρ L - ρ / (1000 * packingLogScale (L / ρ)) := by
    unfold packingAttenuation at ha0
    exact (mul_pos_iff_of_pos_left (by positivity)).mp ha0
  have hfixed := (div_lt_iff₀ hn0).mp (packing_endpoint_loss_lt hχ hgap hρ hρ1 hL n hn)
  have he := packing_frequency_width_mul_length hρ (by linarith : 0 < L)
  have hmain : (n : ℝ) * (bandCancellationRate ρ L - ρ / (1000 * packingLogScale (L / ρ))) ≤
      n * (bandCancellationRate ρ L - 52 * packingFrequencyWidth (L / ρ) * L) - 10 * L := by
    rw [he]
    have hnratio : 0 < (n : ℝ) * (ρ / packingLogScale (L / ρ)) := by positivity
    have hid : ρ / (1000 * packingLogScale (L / ρ)) =
        (1 / 1000 : ℝ) * ρ / packingLogScale (L / ρ) := by ring
    rw [hid]
    simp only [div_eq_mul_inv] at hfixed hnratio ⊢
    nlinarith only [hfixed, hnratio]
  apply (le_div_iff₀ (packingGridSpacing_pos hχ n (geometricPhaseLength θ))).mpr
  calc
    _ = ((999 / 1000 : ℝ) * ((n : ℝ) + geometricPhaseLength θ + 2)) *
        (bandCancellationRate ρ L - ρ / (1000 * packingLogScale (L / ρ))) := by
      unfold packingAttenuation packingGridSpacing
      field_simp [(Real.log_neg hθ0 hθ1).ne]
      <;> ring
    _ ≤ (n : ℝ) * (bandCancellationRate ρ L - ρ / (1000 * packingLogScale (L / ρ))) :=
      mul_le_mul_of_nonneg_right hpadded hδ.le
    _ ≤ _ := hmain

/-- The full finite entropy endpoint term also fits inside the required per-length attenuation. -/
theorem packing_grid_budget_with_endpoint {θ ρ L : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (n : ℕ) (hn : packingBaseLength (-Real.log θ) (L / ρ) ≤ n) :
    packingAttenuation (-Real.log θ) ρ L ≤
      (n * (bandCancellationRate ρ L - 52 * packingFrequencyWidth (L / ρ) * L) -
        (4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) +
          4 * cancellationRemainder (L / ρ)) / cancellationSlope (L / ρ) -
        208 * packingFrequencyWidth (L / ρ)) /
          packingGridSpacing (-Real.log θ) n (geometricPhaseLength θ) := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  apply (packing_grid_attenuation_budget hθ0 hθ1 hgap hρ hρ1 hL n hn).trans
  apply div_le_div_of_nonneg_right _ (packingGridSpacing_pos hχ n _).le
  linarith [packing_entropy_endpoint_error_lt θ hρ hρ1 hL hC]

end LpSelfSimilar.Bernoulli
