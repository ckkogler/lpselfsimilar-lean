module

public import LpSelfSimilar.Fourier.ScaledBandShift

@[expose] public section

/-!
# Digit coordinates of the exact first band shift

The logarithmic ceiling places the first digit coordinate in a half-open
interval of width `kappa`. The angular phase offset is strictly between zero
and two in the required gap range. Integer indices remain explicit until the
nonnegative-start criterion is established.
-/

namespace LpSelfSimilar.Fourier

/-- Angular-to-dyadic offset of the lower band distance. -/
noncomputable def bandPhaseOffset (θ : ℝ) : ℝ := Real.log (Real.pi / θ) / Real.log 2

/-- The phase offset lies strictly between zero and two in the admissible gap range. -/
theorem bandPhaseOffset_bounds {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 70) : 0 < bandPhaseOffset θ ∧ bandPhaseOffset θ < 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg : 1 < Real.pi / θ := by
    apply (lt_div_iff₀ hθ0).mpr
    nlinarith [Real.pi_gt_three]
  have hb := sixteen_pi_div_lt_fifty_two hθ0 hgap
  have hb' : Real.pi / θ < 4 := by
    rw [mul_div_assoc] at hb
    linarith
  unfold bandPhaseOffset
  constructor
  · exact div_pos (Real.log_pos harg) hl
  · apply (div_lt_iff₀ hl).mpr
    have he := Real.log_lt_log (by positivity : 0 < Real.pi / θ) hb'
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rwa [h4] at he

/-- The first shift has the exact half-open coordinate window supplied by its ceiling. -/
theorem bandFirstShift_coordinate_bounds {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (j R : ℝ) :
    j + bandPhaseOffset θ - (-Real.log θ / Real.log 2) <
        R - (-Real.log θ / Real.log 2) *
          (bandFirstShift θ ((2 : ℝ) ^ (-j)) ((2 : ℝ) ^ (-R)) : ℝ) ∧
      R - (-Real.log θ / Real.log 2) *
          (bandFirstShift θ ((2 : ℝ) ^ (-j)) ((2 : ℝ) ^ (-R)) : ℝ) ≤ j + bandPhaseOffset θ := by
  have hκ : 0 < -Real.log θ / Real.log 2 :=
    div_pos (neg_pos.mpr (Real.log_neg hθ0 hθ1)) (Real.log_pos (by norm_num))
  rw [bandFirstShift_dyadic hθ0 hθ1]
  have hlo := Int.le_ceil ((R - j - bandPhaseOffset θ) / (-Real.log θ / Real.log 2))
  have hhi := Int.ceil_lt_add_one ((R - j - bandPhaseOffset θ) / (-Real.log θ / Real.log 2))
  have hlo' := (div_le_iff₀ hκ).mp hlo
  have hhi' := mul_lt_mul_of_pos_right hhi hκ
  rw [add_mul, div_mul_cancel₀ _ hκ.ne', one_mul] at hhi'
  simp only [bandPhaseOffset] at hlo' hhi' ⊢
  constructor <;> nlinarith only [hlo', hhi']

/-- A target beyond the band endpoint gives a nonnegative first digit index. -/
theorem bandFirstShift_nonneg_of_coordinate {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (j R : ℝ) (hR : j + bandPhaseOffset θ ≤ R) :
    0 ≤ bandFirstShift θ ((2 : ℝ) ^ (-j)) ((2 : ℝ) ^ (-R)) := by
  rw [bandFirstShift_dyadic hθ0 hθ1]
  apply Int.ceil_nonneg
  apply div_nonneg
  · change 0 ≤ R - j - bandPhaseOffset θ
    linarith
  · exact (div_pos (neg_pos.mpr (Real.log_neg hθ0 hθ1))
      (Real.log_pos (by norm_num))).le

/-- Extra shifts and digit offsets translate both endpoints by their exact logarithmic distance. -/
theorem shifted_band_digit_coordinate_bounds {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (j R : ℝ) (k i : ℕ) :
    j + bandPhaseOffset θ - (-Real.log θ / Real.log 2) * ((k : ℝ) + i + 1) <
        R - (-Real.log θ / Real.log 2) *
          ((bandFirstShift θ ((2 : ℝ) ^ (-j)) ((2 : ℝ) ^ (-R)) + (k : ℤ) + i : ℤ) : ℝ) ∧
      R - (-Real.log θ / Real.log 2) *
          ((bandFirstShift θ ((2 : ℝ) ^ (-j)) ((2 : ℝ) ^ (-R)) + (k : ℤ) + i : ℤ) : ℝ) ≤
        j + bandPhaseOffset θ - (-Real.log θ / Real.log 2) * ((k : ℝ) + i) := by
  have h := bandFirstShift_coordinate_bounds hθ0 hθ1 j R
  push_cast
  constructor <;> nlinarith [h.1, h.2]

end LpSelfSimilar.Fourier
