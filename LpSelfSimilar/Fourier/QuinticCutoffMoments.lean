module

public import LpSelfSimilar.Fourier.QuinticCutoffInversion

@[expose] public section

/-!
# Integrability of all continuous multiples of the compact frequency cutoff

The cutoff and its first derivative vanish outside the same finite interval.
Continuous frequency multipliers, in particular every polynomial moment, are
therefore integrable against either function. This supplies the domination
needed for spatial differentiation without assuming decay of spatial kernels.
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- Every continuous multiplier times the cutoff or its slope is integrable. -/
theorem integrable_continuous_mul_quinticFourierCutoff_and_slope {ε : ℝ} (hε : 0 < ε)
    {g : ℝ → ℂ} (hg : Continuous g) :
    Integrable (fun ξ => g ξ * (quinticFourierCutoff ε ξ : ℂ)) ∧
      Integrable (fun ξ => g ξ * (quinticFourierCutoffSlope ε ξ : ℂ)) := by
  have hzero (ξ : ℝ) (hξ : ξ ≤ -(1 + ε) ∨ 1 + ε ≤ ξ) : 1 + ε ≤ |ξ| := by
    rcases hξ with hξ | hξ
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl hξ)
  have hc : Continuous (quinticFourierCutoff ε) := continuous_iff_continuousAt.mpr
    (fun ξ => (hasDerivAt_quinticFourierCutoff ε ξ).continuousAt)
  constructor
  · apply integrable_of_intervalIntegrable_zero_off_Ioo
      ((hg.mul (Complex.continuous_ofReal.comp hc)).intervalIntegrable (-(1 + ε)) (1 + ε))
    intro ξ hξ
    change g ξ * (quinticFourierCutoff ε ξ : ℂ) = 0
    rw [quinticFourierCutoff_eq_zero hε (hzero ξ hξ), Complex.ofReal_zero, mul_zero]
  · apply integrable_of_intervalIntegrable_zero_off_Ioo
      ((hg.mul (Complex.continuous_ofReal.comp
        (continuous_quinticFourierCutoffSlope hε.ne'))).intervalIntegrable (-(1 + ε)) (1 + ε))
    intro ξ hξ
    change g ξ * (quinticFourierCutoffSlope ε ξ : ℂ) = 0
    rw [(quinticFourierCutoff_derivatives_zero_off hε (hzero ξ hξ)).1,
      Complex.ofReal_zero, mul_zero]

end LpSelfSimilar.Fourier
