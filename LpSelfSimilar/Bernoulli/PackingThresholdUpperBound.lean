module

public import LpSelfSimilar.Bernoulli.PackingLengths
public import LpSelfSimilar.Bernoulli.SmoothingPrefactor

@[expose] public section

/-!
# Explicit upper bounds for the first usable packing scale

The starting length is a natural ceiling. Its rounding error is absorbed by
one eighth of the unrounded length, and `L+1 <= 4J/3` for `J=L/rho >= 3`.
Together these give the exact coefficient six million used in scale integration.
-/

open LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Rounding the first length costs at most a factor nine eighths. -/
theorem packingBaseLength_upper_bound {χ J : ℝ}
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hJ : 3 ≤ J) :
    (packingBaseLength χ J : ℝ) ≤
      (9 / 8 : ℝ) * (1000000 * J * packingLogScale J / χ) := by
  have ht := six_lt_packingLogScale hJ
  have hprod : 18 ≤ J * packingLogScale J := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hJ) (sub_nonneg.mpr ht.le)]
  have hx : 8 ≤ 1000000 * J * packingLogScale J / χ := by
    apply (le_div_iff₀ hχ).mpr
    nlinarith
  have hceil : (packingBaseLength χ J : ℝ) <
      1000000 * J * packingLogScale J / χ + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith

/-- The actual rounded scale threshold has the stated six-million bound. -/
theorem packingScaleThreshold_upper_bound {χ ρ L : ℝ}
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) :
    packingScaleThreshold χ ρ L ≤
      6000000 * (L / ρ) ^ 2 * packingLogScale (L / ρ) / χ := by
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have ht := six_lt_packingLogScale hJ
  have hLJ : L ≤ L / ρ := by
    apply (le_div_iff₀ hρ).mpr
    nlinarith
  have hcoef : 4 * (L + 1) ≤ (16 / 3 : ℝ) * (L / ρ) := by linarith
  calc
    _ ≤ ((16 / 3 : ℝ) * (L / ρ)) *
        ((9 / 8 : ℝ) * (1000000 * (L / ρ) * packingLogScale (L / ρ) / χ)) :=
      mul_le_mul hcoef (packingBaseLength_upper_bound hχ hχ1 hJ)
        (by positivity) (by positivity)
    _ = _ := by ring

/-- Substituting the threshold gives precisely the prefactor in the integrated estimate. -/
theorem smoothingPrefactor_mul_threshold_div_gap_le {χ ρ L : ℝ}
    (hχ : 0 < χ) (hχ1 : χ ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) :
    2 * smoothingPrefactor χ (L / ρ) * packingScaleThreshold χ ρ L / χ ≤
      2400000000000000000 * (L / ρ) ^ 4 * packingLogScale (L / ρ) ^ 3 / χ ^ 2 *
        (1 + (1 / 1000 : ℝ) / (packingLogScale (L / ρ) * χ)) ^ 2 *
        Real.exp (-1 / (2 * χ)) := by
  have hB := smoothingPrefactor_nonneg χ (L / ρ)
  calc
    _ ≤ 2 * smoothingPrefactor χ (L / ρ) *
        (6000000 * (L / ρ) ^ 2 * packingLogScale (L / ρ) / χ) / χ :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (packingScaleThreshold_upper_bound hχ hχ1 hρ hρ1 hL) (by positivity)) hχ.le
    _ = _ := by unfold smoothingPrefactor; ring

end LpSelfSimilar.Bernoulli
