module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import LpSelfSimilar.Analysis.QuinticSlopeEnergy
public import LpSelfSimilar.Fourier.QuinticSlopeBand
public import LpSelfSimilar.Fourier.QuinticDetailBandIntegrals

@[expose] public section

/-!
# Exact squared derivative energy of the Fourier cutoff

The positive and reflected slope bands have disjoint interiors when epsilon
is at most one. Their squared energies add, even at the touching endpoint.
The affine substitution includes the exact band-width Jacobian, yielding
10/(7*epsilon) with actual integrability proved separately.
-/

open Set MeasureTheory
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- The squared positive slope band is integrable, including its endpoint values. -/
theorem integrable_sq_quinticSlopeBand {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x => quinticSlopeBand ε x ^ 2) := by
  have hc : Continuous (quinticSlopeBand ε) := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_quinticSlopeBand hε.ne' x).continuousAt)
  apply (hc.pow 2).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (1 - ε) (1 + ε)))
  intro x hx
  have ho : x ≤ 1 - ε ∨ 1 + ε ≤ x := by
    by_contra h
    push Not at h
    exact hx ⟨h.1.le, h.2.le⟩
  simp only [Pi.pow_apply]
  rw [(quinticSlopeBand_zero_off hε ho).1, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- A single slope band has squared integral five over seven times the width. -/
theorem integral_sq_quinticSlopeBand {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℝ, quinticSlopeBand ε x ^ 2) = 5 / (7 * ε) := by
  rw [integral_eq_interval_of_eq_zero_off_Ioo (a := 1 - ε) (b := 1 + ε)
    (fun x hx => by rw [(quinticSlopeBand_zero_off hε hx).1]; norm_num)]
  have he : (∫ x in (1 - ε)..(1 + ε), quinticSlopeBand ε x ^ 2) =
      ∫ x in (1 - ε)..(1 + ε),
        quinticTransitionSlope (quinticBandCoordinate ε x) ^ 2 / (2 * ε) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith : 1 - ε ≤ 1 + ε)] at hx
    dsimp only
    rw [quinticSlopeBand, clampedQuinticSlope_eq_of_mem_Icc
      ((quinticBandCoordinate_mem_Icc_iff hε).mpr hx), div_pow]
  rw [he, intervalIntegral.integral_div,
    integral_comp_quinticBandCoordinate hε.ne' (fun u => quinticTransitionSlope u ^ 2),
    integral_sq_quinticTransitionSlope]
  field_simp
  <;> ring

/-- The disjoint positive and reflected bands have additive squared energy at every point. -/
theorem sq_quinticFourierCutoffSlope_eq_bands {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (x : ℝ) :
    quinticFourierCutoffSlope ε x ^ 2 =
      quinticSlopeBand ε x ^ 2 + quinticSlopeBand ε (-x) ^ 2 := by
  rw [quinticFourierCutoffSlope_eq_slopeBands]
  by_cases hx : x ≤ 1 - ε
  · rw [(quinticSlopeBand_zero_off hε (Or.inl hx)).1]
    ring
  · have hn : -x ≤ 1 - ε := by linarith
    rw [(quinticSlopeBand_zero_off hε (Or.inl hn)).1]
    ring

/-- The squared actual cutoff slope is integrable on the whole line. -/
theorem integrable_sq_quinticFourierCutoffSlope {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun x => quinticFourierCutoffSlope ε x ^ 2) := by
  simp_rw [sq_quinticFourierCutoffSlope_eq_bands hε hε1]
  exact (integrable_sq_quinticSlopeBand hε).add (integrable_sq_quinticSlopeBand hε).comp_neg

/-- The exact whole-line squared cutoff slope integral, including both transition bands. -/
theorem integral_sq_quinticFourierCutoffSlope {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x : ℝ, quinticFourierCutoffSlope ε x ^ 2) = 10 / (7 * ε) := by
  simp_rw [sq_quinticFourierCutoffSlope_eq_bands hε hε1]
  rw [integral_add (integrable_sq_quinticSlopeBand hε) (integrable_sq_quinticSlopeBand hε).comp_neg,
    integral_neg_eq_self (fun x => quinticSlopeBand ε x ^ 2) volume,
    integral_sq_quinticSlopeBand hε]
  ring

/-- The same exact energy written with the actual derivative of the cutoff. -/
theorem integral_sq_deriv_quinticFourierCutoff {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ x : ℝ, deriv (quinticFourierCutoff ε) x ^ 2) = 10 / (7 * ε) := by
  simp_rw [(hasDerivAt_quinticFourierCutoff ε _).deriv]
  exact integral_sq_quinticFourierCutoffSlope hε hε1

end LpSelfSimilar.Fourier
