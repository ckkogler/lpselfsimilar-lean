module

public import LpSelfSimilar.Analysis.GeometricBandShift
public import LpSelfSimilar.Analysis.GeometricPhaseConstants
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The first shift of a distance band at a target scale

The exact integer ceiling puts the lower distance into angular phase interval
`(pi,pi/theta]`. Its dyadic expression agrees with the shift used in digit packing.
Every further nonnegative geometric shift keeps the scaled diameter below `52*r`.
-/

namespace LpSelfSimilar.Fourier

/-- First integer shift of a distance band with lower endpoint `a` at scale `r`. -/
noncomputable def bandFirstShift (θ a r : ℝ) : ℤ :=
  Analysis.geometricBandShift θ (a / r) (Real.pi / θ)

/-- The chosen first shift supplies the precise angular base-frequency bounds. -/
theorem bandFirstShift_spec {θ a r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (ha : 0 < a) (hr : 0 < r) :
    Real.pi < (θ ^ bandFirstShift θ a r / r) * a ∧
      (θ ^ bandFirstShift θ a r / r) * a ≤ Real.pi / θ := by
  have h := Analysis.geometricBandShift_spec hθ0 hθ1 (div_pos ha hr)
    (div_pos Real.pi_pos hθ0)
  have he : θ * (Real.pi / θ) = Real.pi := by field_simp
  rw [he] at h
  simpa only [bandFirstShift, div_mul_eq_mul_div, mul_div_assoc] using h

/-- Packing only needs natural digit indices when the unshifted band starts above the target. -/
theorem bandFirstShift_nonneg {θ a r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hstart : Real.pi / θ ≤ a / r) : 0 ≤ bandFirstShift θ a r :=
  Analysis.geometricBandShift_nonneg hθ0 hθ1 (div_pos Real.pi_pos hθ0) hstart

/-- The exact ceiling formula in dyadic scale coordinates, with `kappa=-log(theta)/log(2)`. -/
theorem bandFirstShift_dyadic {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (j R : ℝ) :
    bandFirstShift θ ((2 : ℝ) ^ (-j)) ((2 : ℝ) ^ (-R)) =
      ⌈(R - j - Real.log (Real.pi / θ) / Real.log 2) /
        ((-Real.log θ) / Real.log 2)⌉ := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hj := Real.rpow_pos_of_pos h2 (-j)
  have hR := Real.rpow_pos_of_pos h2 (-R)
  have hlog : Real.log θ ≠ 0 := (Real.log_neg hθ0 hθ1).ne
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  unfold bandFirstShift Analysis.geometricBandShift
  congr 1
  rw [Real.log_div (div_pos hj hR).ne' (div_pos Real.pi_pos hθ0).ne',
    Real.log_div hj.ne' hR.ne', Real.log_rpow h2, Real.log_rpow h2]
  field_simp
  <;> ring

/-- The phase-gap range makes the geometric support constant strictly smaller than 52. -/
theorem sixteen_pi_div_lt_fifty_two {θ : ℝ} (hθ0 : 0 < θ)
    (hgap : -Real.log θ ≤ 1 / 70) : 16 * Real.pi / θ < 52 := by
  have he : Real.exp (-1 / 70) ≤ θ := by
    rw [← Real.exp_log hθ0]
    apply Real.exp_le_exp.mpr
    linarith
  have ht := Analysis.exp_neg_one_seventieth_gt.trans_le he
  apply (div_lt_iff₀ hθ0).mpr
  nlinarith [Real.pi_lt_d6]

/-- Even the full sixteen-band diameter stays below the required translated support width. -/
theorem shifted_band_width_lt {θ a r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 70) (ha : 0 < a) (hr : 0 < r) (k : ℕ) :
    θ ^ (bandFirstShift θ a r + (k : ℤ)) * (16 * a) < 52 * r := by
  have hbase := (bandFirstShift_spec hθ0 hθ1 ha hr).2
  have hb : θ ^ bandFirstShift θ a r * a ≤ Real.pi / θ * r := by
    apply (div_le_iff₀ hr).mp
    simpa only [div_mul_eq_mul_div] using hbase
  have hp : θ ^ k ≤ 1 := pow_le_one₀ hθ0.le hθ1.le
  have hnorm := mul_lt_mul_of_pos_right (sixteen_pi_div_lt_fifty_two hθ0 hgap) hr
  calc
    _ = 16 * (θ ^ bandFirstShift θ a r * a) * θ ^ k := by
      rw [zpow_add₀ hθ0.ne', zpow_natCast]
      ring
    _ ≤ 16 * (θ ^ bandFirstShift θ a r * a) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
        (by positivity : 0 ≤ 16 * (θ ^ bandFirstShift θ a r * a))
    _ ≤ 16 * (Real.pi / θ * r) := by linarith
    _ = (16 * Real.pi / θ) * r := by ring
    _ < 52 * r := hnorm

end LpSelfSimilar.Fourier
