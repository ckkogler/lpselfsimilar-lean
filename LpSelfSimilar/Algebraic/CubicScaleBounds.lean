module

public import LpSelfSimilar.Algebraic.CubicCriterionParameters
public import LpSelfSimilar.Algebraic.DegreeMahlerPowers
public import LpSelfSimilar.Analysis.CubicScaleConstraints

@[expose] public section

/-!
# Canonical scale bounds from the exact cubic hypothesis

All real scale constraints are supplied by the canonical algebraic degree,
Mahler measure and gap estimate. Equality in the displayed cubic hypothesis
is retained. This supplies B>8 and the stronger B>11 in the low-Mahler branch.
-/

open Real
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Algebraic

/-- Canonical algebraic data supply every scale bound used in the two cases. -/
theorem cubic_hypothesis_scale_bounds {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1)
    (hcubic : 1 - (min 1 (log (mahlerMeasure x)) / degreeMahlerScale x) ^ 3 ≤ x) :
    let s := min 1 (log (mahlerMeasure x))
    let B := degreeMahlerScale x / s
    0 < s ∧ 3 ≤ B ∧ degreeMahlerScale x ≤ B ∧ (1 - x) * B ^ 3 ≤ 1 ∧
      8 < B ∧ (log (mahlerMeasure x) < 2 → 11 < B) ∧ 3 * log B / B ≤ s := by
  let m := log (mahlerMeasure x)
  let s := min 1 m
  let D := degreeMahlerScale x
  let B := D / s
  change 0 < s ∧ 3 ≤ B ∧ D ≤ B ∧ (1 - x) * B ^ 3 ≤ 1 ∧
    8 < B ∧ (m < 2 → 11 < B) ∧ 3 * log B / B ≤ s
  have hm : 0 < m := log_pos (one_lt_mahlerMeasure hx hx0 hx1)
  have hs : 0 < s := lt_min zero_lt_one hm
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsm : s ≤ m := min_le_right _ _
  have hD0 : 0 < D := degreeMahlerScale_pos hx
  have hd : (1 : ℝ) ≤ algebraicDegree x := by exact_mod_cast algebraicDegree_pos hx
  have hB3 : 3 ≤ B := by
    apply (le_div_iff₀ hs).mpr
    change 3 * s ≤ 1 + (algebraicDegree x : ℝ) + m
    linarith
  have hB0 : 0 < B := by linarith
  have hDB : D ≤ B := (le_div_iff₀ hs).mpr (mul_le_of_le_one_right hD0.le hs1)
  have hi : s / D = 1 / B := by dsimp [B]; field_simp
  have hc : 1 - (s / D) ^ 3 ≤ x := hcubic
  rw [hi, div_pow, one_pow] at hc
  have hcube : (1 - x) * B ^ 3 ≤ 1 :=
    (le_div_iff₀ (pow_pos hB0 3)).mp (by linarith)
  have hg : 0 < 1 - x := sub_pos.mpr hx1
  have hgap := log_inverse_gap_le_degree_mahler hx hx0 hx1
  have hB8 : 8 < B := cubic_scale_eight_lt hg hB3 hd hDB hcube hgap
  have hB11 : m < 2 → 11 < B := fun h => cubic_scale_eleven_lt hg hB3 h hDB hcube hgap
  have he : s * B = 1 + (algebraicDegree x : ℝ) + m := by
    change s * (D / s) = D
    field_simp
  exact ⟨hs, hB3, hDB, hcube, hB8, hB11,
    cubic_entropy_factor_lower_bound hg hB0 hd he hcube hgap⟩

end LpSelfSimilar.Algebraic
