module

public import LpSelfSimilar.Fourier.BandShiftCoordinates
public import LpSelfSimilar.Analysis.GeometricPhaseLength
public import LpSelfSimilar.Analysis.PackingNumericalBounds

@[expose] public section

/-!
# Digit windows and nonnegative starts for retained bands

The exact first-shift ceiling and bounded extra phase shift locate every digit
in the required logarithmic window. A target beyond `4*(L+1)*n` makes each first
shift nonnegative. Compact support or a priori index restrictions are not assumed.
-/

open LpSelfSimilar.Analysis LpSelfSimilar.Fourier

namespace LpSelfSimilar.Bernoulli

/-- The full extra phase range occupies fewer than thirty dyadic coordinate units. -/
theorem packing_phase_coordinate_width_lt {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) :
    (-Real.log θ / Real.log 2) * ((geometricPhaseLength θ : ℝ) + 1) < 30 := by
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : (geometricPhaseLength θ : ℝ) < Real.log 10000 / (-Real.log θ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hKχ := mul_lt_mul_of_pos_right hK hχ
  rw [add_mul, div_mul_cancel₀ _ hχ.ne', one_mul] at hKχ
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hl).mpr
  nlinarith [Real.log_two_gt_d9, log_ten_thousand_lt_ten]

/-- Every digit of a retained band block lies in its prescribed logarithmic window. -/
theorem packing_digit_coordinate_window {θ ρ L : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (n : ℕ) (j R : ℝ)
    (hj : j ∈ Set.Icc ((4 / 25 : ℝ) * ρ * n) (L * n + 4))
    (k i : ℕ) (hk : k ≤ geometricPhaseLength θ) (hi : i < n) :
    ((4 / 25 : ℝ) * ρ - (-Real.log θ / Real.log 2)) * n - 30 <
        R - (-Real.log θ / Real.log 2) *
          ((bandFirstShift θ ((2 : ℝ) ^ (-j)) ((2 : ℝ) ^ (-R)) + (k : ℤ) + i : ℤ) : ℝ) ∧
      R - (-Real.log θ / Real.log 2) *
          ((bandFirstShift θ ((2 : ℝ) ^ (-j)) ((2 : ℝ) ^ (-R)) + (k : ℤ) + i : ℤ) : ℝ) ≤
        L * n + 34 := by
  have hκ : 0 < -Real.log θ / Real.log 2 :=
    div_pos (neg_pos.mpr (Real.log_neg hθ0 hθ1)) (Real.log_pos (by norm_num))
  have hC := bandPhaseOffset_bounds hθ0 hθ1 (by linarith : -Real.log θ ≤ 1 / 70)
  have hwidth := packing_phase_coordinate_width_lt hθ0 hθ1 hgap
  have hcoord := shifted_band_digit_coordinate_bounds hθ0 hθ1 j R k i
  have hindices : (k : ℝ) + i + 1 ≤ (geometricPhaseLength θ : ℝ) + n := by
    exact_mod_cast (show k + i + 1 ≤ geometricPhaseLength θ + n from by omega)
  have hmul := mul_le_mul_of_nonneg_left hindices hκ.le
  have hnonneg : 0 ≤ (-Real.log θ / Real.log 2) * ((k : ℝ) + i) := by positivity
  constructor
  · nlinarith [hcoord.1, hC.1, hj.1]
  · nlinarith [hcoord.2, hC.2, hj.2]

/-- The frequency cutoff forces nonnegative first digit indices at each selected length. -/
theorem packing_band_first_shift_nonneg {θ L : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hL : 3 ≤ L) (n : ℕ) (hn : 0 < n)
    (j R : ℝ) (hj : j ≤ L * n + 4) (hR : 4 * (L + 1) * n ≤ R) :
    0 ≤ bandFirstShift θ ((2 : ℝ) ^ (-j)) ((2 : ℝ) ^ (-R)) := by
  have hC := bandPhaseOffset_bounds hθ0 hθ1 (by linarith : -Real.log θ ≤ 1 / 70)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLn : 3 * (n : ℝ) ≤ L * n := mul_le_mul_of_nonneg_right hL (Nat.cast_nonneg n)
  apply bandFirstShift_nonneg_of_coordinate hθ0 hθ1 j R
  nlinarith [hC.2]

end LpSelfSimilar.Bernoulli
