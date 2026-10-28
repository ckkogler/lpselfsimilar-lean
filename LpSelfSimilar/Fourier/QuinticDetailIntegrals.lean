module

public import LpSelfSimilar.Fourier.QuinticDetailBandIntegrals
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

@[expose] public section

/-!
# Zeroth and first absolute integral bounds for the actual detail multiplier

The reflected-band identity gives exact total mass two. The first derivative
bound follows by the integral triangle inequality and is stated for the actual
`deriv`, preserving the constant seven.
-/

open Set MeasureTheory
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- The positive-band detail is nonnegative everywhere. -/
theorem quinticDetailBand_nonneg {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x : ℝ) :
    0 ≤ quinticDetailBand ε x := by
  by_cases hx : x ∈ Icc (1 - ε) (1 + ε)
  · rw [quinticDetailBand_eq_profile hε hx]
    exact div_nonneg (quinticDetailProfile_nonneg hε.le hε1
      ((quinticBandCoordinate_mem_Icc_iff hε).mpr hx)) (by positivity)
  · have he : x ≤ 1 - ε ∨ 1 + ε ≤ x := by
      by_cases h : x ≤ 1 - ε
      · exact Or.inl h
      · exact Or.inr (le_of_not_ge (fun h' ↦ hx ⟨(lt_of_not_ge h).le, h'⟩))
    rw [(quinticDetailBand_eq_zero hε he).1]

/-- The actual even detail is nonnegative everywhere. -/
theorem quinticFourierDetail_nonneg {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x : ℝ) :
    0 ≤ quinticFourierDetail ε x := by
  rw [quinticFourierDetail_eq_bands]
  exact add_nonneg (quinticDetailBand_nonneg hε hε1 x) (quinticDetailBand_nonneg hε hε1 (-x))

/-- The actual detail multiplier is integrable. -/
theorem integrable_quinticFourierDetail {ε : ℝ} (hε : 0 < ε) :
    Integrable (quinticFourierDetail ε) := by
  have he : quinticFourierDetail ε = fun x ↦ quinticDetailBand ε x + quinticDetailBand ε (-x) :=
    funext (quinticFourierDetail_eq_bands ε)
  rw [he]
  exact (integrable_quinticDetailBand hε).add (integrable_quinticDetailBand hε).comp_neg

/-- The actual first derivative of the detail multiplier is integrable. -/
theorem integrable_deriv_quinticFourierDetail {ε : ℝ} (hε : 0 < ε) :
    Integrable (deriv (quinticFourierDetail ε)) := by
  have he : deriv (quinticFourierDetail ε) = fun x ↦
      quinticDetailBandSlope ε x - quinticDetailBandSlope ε (-x) := by
    funext x
    rw [(hasDerivAt_quinticFourierDetail (ne_of_gt hε) x).deriv,
      quinticFourierDetailSlope_eq_bands]
  rw [he]
  exact (integrable_quinticDetailBandSlope hε).sub (integrable_quinticDetailBandSlope hε).comp_neg

/-- The exact total absolute mass of the detail multiplier is two. -/
theorem integral_abs_quinticFourierDetail {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x, |quinticFourierDetail ε x|) = 2 := by
  have he : (fun x ↦ |quinticFourierDetail ε x|) = fun x ↦
      |quinticDetailBand ε x| + |quinticDetailBand ε (-x)| := by
    funext x
    rw [abs_of_nonneg (quinticFourierDetail_nonneg hε hε1 x),
      abs_of_nonneg (quinticDetailBand_nonneg hε hε1 x),
      abs_of_nonneg (quinticDetailBand_nonneg hε hε1 (-x)), quinticFourierDetail_eq_bands]
  rw [he, integral_add (integrable_quinticDetailBand hε).abs
    (integrable_quinticDetailBand hε).abs.comp_neg,
    integral_neg_eq_self (fun x ↦ |quinticDetailBand ε x|) volume, integral_abs_quinticDetailBand hε hε1]
  norm_num

/-- The actual first derivative's absolute integral satisfies its rescaled profile bound. -/
theorem integral_abs_deriv_quinticFourierDetail_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x, |deriv (quinticFourierDetail ε) x|) ≤ (6 + 8 * ε) / ε := by
  have he (x : ℝ) : |deriv (quinticFourierDetail ε) x| ≤
      |quinticDetailBandSlope ε x| + |quinticDetailBandSlope ε (-x)| := by
    rw [(hasDerivAt_quinticFourierDetail (ne_of_gt hε) x).deriv,
      quinticFourierDetailSlope_eq_bands]
    exact abs_sub _ _
  have h := integral_mono (integrable_deriv_quinticFourierDetail hε).abs
    ((integrable_quinticDetailBandSlope hε).abs.add (integrable_quinticDetailBandSlope hε).abs.comp_neg) he
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_quinticDetailBandSlope hε).abs
    (integrable_quinticDetailBandSlope hε).abs.comp_neg, integral_neg_eq_self (fun x ↦ |quinticDetailBandSlope ε x|) volume] at h
  have hb := integral_abs_quinticDetailBandSlope_le hε hε1
  have heq : (6 + 8 * ε) / ε = 2 * ((6 + 8 * ε) / (2 * ε)) := by ring
  rw [heq]
  linarith

/-- The first two constants in the Fourier detail estimates, for the actual derivative. -/
theorem quinticFourierDetail_first_integral_bounds {ε : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 100000) :
    (∫ x, |quinticFourierDetail ε x|) ≤ 21 / 10 ∧
      (∫ x, |deriv (quinticFourierDetail ε) x|) ≤ 7 / ε := by
  have hε1 : ε ≤ 1 := by linarith
  constructor
  · rw [integral_abs_quinticFourierDetail hε hε1]
    norm_num
  · exact (integral_abs_deriv_quinticFourierDetail_le hε hε1).trans
      (div_le_div_of_nonneg_right (by linarith : 6 + 8 * ε ≤ 7) hε.le)

end LpSelfSimilar.Fourier
