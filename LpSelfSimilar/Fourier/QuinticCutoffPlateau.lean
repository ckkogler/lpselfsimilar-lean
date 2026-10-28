module

public import LpSelfSimilar.Fourier.QuinticCutoffSupport

@[expose] public section

/-!
# Derivatives on the closed plateau of the quintic cutoff

Both transition slopes and curvatures vanish at the inner endpoints. Thus the
actual derivatives vanish throughout the closed plateau, including its joins.
A rescaled unit-angle interval lies in this plateau whenever its small scale
is at most 1-epsilon.
-/

open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- Both explicit derivatives vanish on the closed central plateau. -/
theorem quinticFourierCutoff_slope_curvature_eq_zero_on_plateau {ε x : ℝ}
    (hε : 0 < ε) (hx : |x| ≤ 1 - ε) :
    quinticFourierCutoffSlope ε x = 0 ∧ quinticFourierCutoffCurvature ε x = 0 := by
  have hp := (quinticBandCoordinate_nonpos_iff hε).mpr (abs_le.mp hx).2
  have hn := (quinticBandCoordinate_nonpos_iff hε).mpr
    (show -x ≤ 1 - ε by linarith [(abs_le.mp hx).1])
  simp only [quinticFourierCutoffSlope, quinticFourierCutoffCurvature,
    clampedQuinticSlope_eq_zero (Or.inl hp), clampedQuinticSlope_eq_zero (Or.inl hn),
    clampedQuinticCurvature_eq_zero (Or.inl hp), clampedQuinticCurvature_eq_zero (Or.inl hn),
    sub_self, zero_add, zero_div, and_self]

/-- The actual cutoff derivative vanishes even at the inner transition endpoints. -/
theorem hasDerivAt_quinticFourierCutoff_zero_on_plateau {ε x : ℝ}
    (hε : 0 < ε) (hx : |x| ≤ 1 - ε) : HasDerivAt (quinticFourierCutoff ε) 0 x := by
  simpa only [(quinticFourierCutoff_slope_curvature_eq_zero_on_plateau hε hx).1] using
    hasDerivAt_quinticFourierCutoff ε x

/-- A small scaled unit-angle interval lies within the exact cutoff plateau. -/
theorem quinticFourierCutoff_scaled_eq_one {ε χ a u : ℝ}
    (hε : 0 < ε) (hχ : 0 ≤ χ) (hscale : χ ≤ 1 - ε) (hu : |a * u| ≤ 1) :
    quinticFourierCutoff ε (χ * a * u) = 1 := by
  apply quinticFourierCutoff_eq_one hε
  calc
    |χ * a * u| = χ * |a * u| := by rw [mul_assoc, abs_mul, abs_of_nonneg hχ]
    _ ≤ χ := by nlinarith
    _ ≤ 1 - ε := hscale

/-- The actual derivative of the rescaled cutoff vanishes on that closed interval. -/
theorem hasDerivAt_quinticFourierCutoff_scaled_zero {ε χ a u : ℝ}
    (hε : 0 < ε) (hχ : 0 ≤ χ) (hscale : χ ≤ 1 - ε) (hu : |a * u| ≤ 1) :
    HasDerivAt (fun v => quinticFourierCutoff ε (χ * a * v)) 0 u := by
  have hx : |χ * a * u| ≤ 1 - ε := by
    rw [mul_assoc, abs_mul, abs_of_nonneg hχ]
    exact (mul_le_mul_of_nonneg_left hu hχ).trans (by simpa only [mul_one] using hscale)
  have h := (hasDerivAt_quinticFourierCutoff_zero_on_plateau hε hx).comp u
    ((hasDerivAt_id u).const_mul (χ * a))
  simpa only [Function.comp_def, id_eq, mul_one, zero_mul] using! h

end LpSelfSimilar.Fourier
