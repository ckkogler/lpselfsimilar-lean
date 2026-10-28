module

public import LpSelfSimilar.Fourier.QuinticDetailBand
public import LpSelfSimilar.Analysis.SupportedIntervalIntegral

@[expose] public section

/-!
# Whole-line integral estimates for a single detail band

The actual globally defined band function and slope are integrable. The affine
change of variables transfers the polynomial estimates with the exact powers
of the band width; the band mass is one.
-/

open Set MeasureTheory
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- Exact affine change of variables from the spatial band to the unit interval. -/
theorem integral_comp_quinticBandCoordinate {ε : ℝ} (hε : ε ≠ 0) (f : ℝ → ℝ) :
    (∫ x in (1 - ε)..(1 + ε), f (quinticBandCoordinate ε x)) =
      (2 * ε) * ∫ u in (0 : ℝ)..1, f u := by
  unfold quinticBandCoordinate
  rw [intervalIntegral.integral_comp_sub_right (fun x ↦ f (x / (2 * ε))) (1 - ε)]
  rw [intervalIntegral.integral_comp_div f (mul_ne_zero (by norm_num) hε)]
  have he : (1 + ε - (1 - ε)) / (2 * ε) = 1 := by field_simp; ring
  rw [he]
  simp only [sub_self, zero_div, smul_eq_mul]

/-- The actual band function is integrable on the real line. -/
theorem integrable_quinticDetailBand {ε : ℝ} (hε : 0 < ε) :
    Integrable (quinticDetailBand ε) :=
  (continuous_iff_continuousAt.mpr (fun x ↦
    (hasDerivAt_quinticDetailBand (ne_of_gt hε) x).continuousAt)).integrable_of_hasCompactSupport
      (hasCompactSupport_quinticDetailBand hε)

/-- The actual band slope is continuous, even at the transition endpoints. -/
theorem continuous_quinticDetailBandSlope (ε : ℝ) :
    Continuous (quinticDetailBandSlope ε) := by
  have hs : Continuous clampedQuinticSlope := continuous_iff_continuousAt.mpr
    (fun u ↦ (hasDerivAt_clampedQuinticSlope u).continuousAt)
  have hc : Continuous (quinticBandCoordinate ε) := by unfold quinticBandCoordinate; fun_prop
  unfold quinticDetailBandSlope
  exact ((hs.comp hc).neg.div_const _).sub
    ((continuous_id.mul (continuous_clampedQuinticCurvature.comp hc)).div_const _)

/-- The actual band slope is integrable on the real line. -/
theorem integrable_quinticDetailBandSlope {ε : ℝ} (hε : 0 < ε) :
    Integrable (quinticDetailBandSlope ε) :=
  (continuous_quinticDetailBandSlope ε).integrable_of_hasCompactSupport
    (hasCompactSupport_quinticDetailBandSlope hε)

/-- The actual positive-band multiplier has absolute integral exactly one. -/
theorem integral_abs_quinticDetailBand {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x, |quinticDetailBand ε x|) = 1 := by
  rw [integral_eq_interval_of_eq_zero_off_Ioo (a := 1 - ε) (b := 1 + ε)
    (fun x hx ↦ by rw [(quinticDetailBand_eq_zero hε hx).1, abs_zero])]
  have he : (∫ x in (1 - ε)..(1 + ε), |quinticDetailBand ε x|) =
      ∫ x in (1 - ε)..(1 + ε),
        |quinticDetailProfile ε (quinticBandCoordinate ε x)| / (2 * ε) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : 1 - ε ≤ 1 + ε)] at hx
    dsimp only
    rw [quinticDetailBand_eq_profile hε hx, abs_div, abs_of_pos (by positivity : 0 < 2 * ε)]
  rw [he, intervalIntegral.integral_div,
    integral_comp_quinticBandCoordinate (ne_of_gt hε) (fun u ↦ |quinticDetailProfile ε u|),
    integral_abs_quinticDetailProfile hε.le hε1]
  field_simp

/-- The actual band slope has the exact rescaled absolute profile integral. -/
theorem integral_abs_quinticDetailBandSlope_eq {ε : ℝ} (hε : 0 < ε) :
    (∫ x, |quinticDetailBandSlope ε x|) =
      (∫ u in (0 : ℝ)..1, |quinticDetailProfileSlope ε u|) / (2 * ε) := by
  rw [integral_eq_interval_of_eq_zero_off_Ioo (a := 1 - ε) (b := 1 + ε)
    (fun x hx ↦ by rw [(quinticDetailBand_eq_zero hε hx).2, abs_zero])]
  have he : (∫ x in (1 - ε)..(1 + ε), |quinticDetailBandSlope ε x|) =
      ∫ x in (1 - ε)..(1 + ε),
        |quinticDetailProfileSlope ε (quinticBandCoordinate ε x)| / (2 * ε) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : 1 - ε ≤ 1 + ε)] at hx
    dsimp only
    rw [quinticDetailBandSlope_eq_profile hε hx, abs_div, abs_of_nonneg (sq_nonneg (2 * ε))]
  rw [he, intervalIntegral.integral_div, integral_comp_quinticBandCoordinate (ne_of_gt hε) (fun u ↦ |quinticDetailProfileSlope ε u|)]
  field_simp
  <;> ring

/-- The single-band slope's absolute integral is bounded with no loss in scaling. -/
theorem integral_abs_quinticDetailBandSlope_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x, |quinticDetailBandSlope ε x|) ≤ (6 + 8 * ε) / (2 * ε) := by
  rw [integral_abs_quinticDetailBandSlope_eq hε]
  exact div_le_div_of_nonneg_right
    (integral_abs_quinticDetailProfileSlope_le hε.le hε1) (by positivity)

end LpSelfSimilar.Fourier
