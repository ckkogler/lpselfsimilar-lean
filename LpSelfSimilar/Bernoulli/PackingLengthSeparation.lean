module

public import LpSelfSimilar.Bernoulli.PackingParameters

@[expose] public section

/-!
# Separating windows of different block lengths

The quadratic smallness hypothesis makes the dyadic gap less than `0.021*rho`.
The integer length multiplier then separates successive windows by more than
`1.25*L`, while the first length absorbs their fixed endpoints. All statements
concern explicit numerical parameters and actual natural block lengths.
-/

open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Even after multiplication by the entropy rate, the first block length exceeds one thousand. -/
theorem packingBaseLength_entropy_mul_gt {χ ρ L : ℝ} (hχ : 0 < χ) (hχ1 : χ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) :
    (1000 : ℝ) < ρ * (packingBaseLength χ (L / ρ) : ℝ) := by
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have ht := six_lt_packingLogScale hJ
  have hb := (div_le_iff₀ hχ).mp (packingBaseLength_lower_bound χ (L / ρ))
  have hp := mul_le_mul_of_nonneg_left hb hρ.le
  have he : ρ * (1000000 * (L / ρ) * packingLogScale (L / ρ)) =
      1000000 * L * packingLogScale (L / ρ) := by field_simp
  rw [he] at hp
  have hcap := mul_le_mul_of_nonneg_left hχ1
    (by positivity : 0 ≤ ρ * (packingBaseLength χ (L / ρ) : ℝ))
  have hLt : (18 : ℝ) < L * packingLogScale (L / ρ) := by nlinarith
  nlinarith

/-- The dyadic contraction gap is below the rational margin used for window separation. -/
theorem packing_dyadic_gap_lt {χ ρ L : ℝ} (hχ : 0 < χ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : χ * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2) :
    χ / Real.log 2 < (21 / 1000 : ℝ) * ρ := by
  have hg := (div_lt_iff₀ hρ).mp (packing_gap_div_entropy_lt hχ hρ hρ1 hL hsmall)
  have hl : (69 / 100 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hp := mul_lt_mul_of_pos_right hl (by positivity : 0 < (21 / 1000 : ℝ) * ρ)
  apply (div_lt_iff₀ (by positivity : 0 < Real.log 2)).mpr
  nlinarith

/-- Successive length multipliers expand the lower window endpoint by more than `1.25*L`. -/
theorem packingLengthMultiplier_window_slope_gt {χ ρ L : ℝ} (hχ : 0 < χ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : χ * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2) :
    (5 / 4 : ℝ) * L < (packingLengthMultiplier (L / ρ) : ℝ) *
      ((4 / 25 : ℝ) * ρ - χ / Real.log 2) := by
  have hg := packing_dyadic_gap_lt hχ hρ hρ1 hL hsmall
  have hD : (139 / 1000 : ℝ) * ρ < (4 / 25 : ℝ) * ρ - χ / Real.log 2 := by linarith
  have hN := (packingLengthMultiplier_bounds (three_le_separation_entropy_ratio hρ hρ1 hL)).1
  calc
    _ < (1251 / 1000 : ℝ) * L := by nlinarith
    _ = (9 * (L / ρ)) * ((139 / 1000 : ℝ) * ρ) := by field_simp; ring
    _ < (9 * (L / ρ)) * ((4 / 25 : ℝ) * ρ - χ / Real.log 2) :=
      mul_lt_mul_of_pos_left hD (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hN (by nlinarith)

/-- At any retained block length the multiplicative margin exceeds the fixed window padding. -/
theorem packing_length_padding_margin {χ ρ L : ℝ} (hχ : 0 < χ) (hχ1 : χ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (n : ℕ)
    (hn : packingBaseLength χ (L / ρ) ≤ n) :
    (64 : ℝ) < (1 / 4 : ℝ) * L * n := by
  have hbase := packingBaseLength_entropy_mul_gt hχ hχ1 hρ hρ1 hL
  have hρn : (1000 : ℝ) < ρ * (n : ℝ) :=
    hbase.trans_le (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hρ.le)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hρn' := mul_le_mul_of_nonneg_right hρ1 hn0
  have hLn := mul_le_mul_of_nonneg_right hL hn0
  nlinarith

/-- Every retained length has its entire digit window strictly above coordinate two. -/
theorem packing_window_lower_gt_two {χ ρ L : ℝ} (hχ : 0 < χ) (hχ1 : χ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : χ * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (n : ℕ) (hn : packingBaseLength χ (L / ρ) ≤ n) :
    (2 : ℝ) < ((4 / 25 : ℝ) * ρ - χ / Real.log 2) * n - 30 := by
  have hρn : (1000 : ℝ) < ρ * (n : ℝ) :=
    (packingBaseLength_entropy_mul_gt hχ hχ1 hρ hρ1 hL).trans_le
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hρ.le)
  have hn0 : (0 : ℝ) < n := by nlinarith
  have hg := packing_dyadic_gap_lt hχ hρ hρ1 hL hsmall
  have hD : (139 / 1000 : ℝ) * ρ < (4 / 25 : ℝ) * ρ - χ / Real.log 2 := by linarith
  have hp := mul_lt_mul_of_pos_right hD hn0
  nlinarith

/-- Windows of two block lengths separated by the integer multiplier are strictly disjoint. -/
theorem packing_length_windows_separated {χ ρ L : ℝ} (hχ : 0 < χ) (hχ1 : χ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : χ * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (n n' : ℕ) (hn : packingBaseLength χ (L / ρ) ≤ n)
    (hn' : packingLengthMultiplier (L / ρ) * n ≤ n') :
    L * n + 34 < ((4 / 25 : ℝ) * ρ - χ / Real.log 2) * n' - 30 := by
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le (packingBaseLength_pos hχ hJ) hn
  have hg := packing_dyadic_gap_lt hχ hρ hρ1 hL hsmall
  have hD : 0 < (4 / 25 : ℝ) * ρ - χ / Real.log 2 := by nlinarith
  have hstep : (packingLengthMultiplier (L / ρ) : ℝ) * n ≤ (n' : ℝ) := by exact_mod_cast hn'
  have hp := mul_le_mul_of_nonneg_left hstep hD.le
  have hmult := mul_lt_mul_of_pos_right
    (packingLengthMultiplier_window_slope_gt hχ hρ hρ1 hL hsmall) hn0
  have hpad := packing_length_padding_margin hχ hχ1 hρ hρ1 hL n hn
  nlinarith

end LpSelfSimilar.Bernoulli
