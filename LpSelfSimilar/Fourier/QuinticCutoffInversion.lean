module

public import LpSelfSimilar.Fourier.QuinticDetailInversion

@[expose] public section

/-!
# Integrability of the smoothing cutoff's inverse transform

The smoothing cutoff itself has a continuous second derivative. Its value and
first derivative vanish at the two outer endpoints, so ordinary interval
integration by parts gives an integrable inverse transform. This complements
the piecewise argument needed for its detail multiplier.
-/

open Set MeasureTheory
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- Both cutoff derivatives vanish at and beyond the outer support endpoints. -/
theorem quinticFourierCutoff_derivatives_zero_off {ε x : ℝ} (hε : 0 < ε)
    (hx : 1 + ε ≤ |x|) :
    quinticFourierCutoffSlope ε x = 0 ∧ quinticFourierCutoffCurvature ε x = 0 := by
  have hcoord (y : ℝ) (hy : 1 + ε ≤ |y|) :
      quinticBandCoordinate ε y ≤ 0 ∨ 1 ≤ quinticBandCoordinate ε y := by
    rcases le_abs.mp hy with hy | hy
    · exact Or.inr ((one_le_quinticBandCoordinate_iff hε).mpr hy)
    · exact Or.inl ((quinticBandCoordinate_nonpos_iff hε).mpr (by linarith))
  have hp := hcoord x hx
  have hn := hcoord (-x) (by simpa only [abs_neg] using hx)
  simp [quinticFourierCutoffSlope, quinticFourierCutoffCurvature,
    clampedQuinticSlope_eq_zero hp, clampedQuinticSlope_eq_zero hn,
    clampedQuinticCurvature_eq_zero hp, clampedQuinticCurvature_eq_zero hn]

/-- Continuity of the first derivative of the smoothing cutoff. -/
theorem continuous_quinticFourierCutoffSlope {ε : ℝ} (hε : ε ≠ 0) :
    Continuous (quinticFourierCutoffSlope ε) :=
  continuous_iff_continuousAt.mpr (fun x ↦ (hasDerivAt_quinticFourierCutoffSlope hε x).continuousAt)

/-- The smoothing cutoff and its curvature are integrable as complex amplitudes. -/
theorem integrable_quinticFourierCutoff_and_curvature {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun ξ ↦ (quinticFourierCutoff ε ξ : ℂ)) ∧
      Integrable (fun ξ ↦ (quinticFourierCutoffCurvature ε ξ : ℂ)) := by
  have hzero (ξ : ℝ) (hξ : ξ ≤ -(1 + ε) ∨ 1 + ε ≤ ξ) : 1 + ε ≤ |ξ| := by
    rcases hξ with hξ | hξ
    · exact (le_abs.mpr (Or.inr (by linarith)))
    · exact (le_abs.mpr (Or.inl hξ))
  have hc : Continuous (quinticFourierCutoff ε) := continuous_iff_continuousAt.mpr
    (fun ξ ↦ (hasDerivAt_quinticFourierCutoff ε ξ).continuousAt)
  constructor
  · apply integrable_of_intervalIntegrable_zero_off_Ioo
      ((Complex.continuous_ofReal.comp hc).intervalIntegrable (-(1 + ε)) (1 + ε))
    intro ξ hξ
    dsimp only [Function.comp_apply]
    rw [quinticFourierCutoff_eq_zero hε (hzero ξ hξ), Complex.ofReal_zero]
  · apply integrable_of_intervalIntegrable_zero_off_Ioo
      ((Complex.continuous_ofReal.comp (continuous_quinticFourierCutoffCurvature ε)).intervalIntegrable
        (-(1 + ε)) (1 + ε))
    intro ξ hξ
    dsimp only [Function.comp_apply]
    rw [(quinticFourierCutoff_derivatives_zero_off hε (hzero ξ hξ)).2, Complex.ofReal_zero]

/-- The actual smoothing cutoff satisfies the twice-integrated Fourier identity. -/
theorem angularFourier_quinticCutoff_secondDerivative {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (∫ ξ, angularFourierPhase x ξ * (quinticFourierCutoffCurvature ε ξ : ℂ)) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * (quinticFourierCutoff ε ξ : ℂ) := by
  have hzero (ξ : ℝ) (hξ : ξ ≤ -(1 + ε) ∨ 1 + ε ≤ ξ) : 1 + ε ≤ |ξ| := by
    rcases hξ with hξ | hξ
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl hξ)
  have hc : Continuous (quinticFourierCutoff ε) := continuous_iff_continuousAt.mpr
    (fun ξ ↦ (hasDerivAt_quinticFourierCutoff ε ξ).continuousAt)
  apply angularFourier_secondDerivative_identity_of_interval (a := -(1 + ε)) (b := 1 + ε)
    (g' := fun ξ ↦ (quinticFourierCutoffSlope ε ξ : ℂ)) (by linarith)
    (Complex.continuous_ofReal.comp hc).continuousOn
    (Complex.continuous_ofReal.comp (continuous_quinticFourierCutoffSlope (ne_of_gt hε))).continuousOn
    (fun ξ hξ ↦ (hasDerivAt_quinticFourierCutoff ε ξ).ofReal_comp)
    (fun ξ hξ ↦ (hasDerivAt_quinticFourierCutoffSlope (ne_of_gt hε) ξ).ofReal_comp)
    ((Complex.continuous_ofReal.comp (continuous_quinticFourierCutoffCurvature ε)).intervalIntegrable _ _)
  · intro ξ hξ
    dsimp only [Function.comp_apply]
    rw [quinticFourierCutoff_eq_zero hε (hzero ξ hξ), Complex.ofReal_zero]
  · intro ξ hξ
    change (quinticFourierCutoffCurvature ε ξ : ℂ) = 0
    rw [(quinticFourierCutoff_derivatives_zero_off hε (hzero ξ hξ)).2, Complex.ofReal_zero]
  · rw [(quinticFourierCutoff_derivatives_zero_off hε (hzero (-(1 + ε)) (Or.inl le_rfl))).1,
      Complex.ofReal_zero]
  · rw [(quinticFourierCutoff_derivatives_zero_off hε (hzero (1 + ε) (Or.inr le_rfl))).1,
      Complex.ofReal_zero]

/-- The smoothing cutoff has an integrable, continuous inverse Fourier kernel. -/
theorem integrable_continuous_angularInverseFourier_quinticCutoff {ε : ℝ} (hε : 0 < ε) :
    Integrable (angularInverseFourier (fun ξ ↦ (quinticFourierCutoff ε ξ : ℂ))) ∧
      Continuous (angularInverseFourier (fun ξ ↦ (quinticFourierCutoff ε ξ : ℂ))) := by
  have hi := integrable_quinticFourierCutoff_and_curvature hε
  exact ⟨integrable_angularInverseFourier_of_secondDerivative_identity hi.1 hi.2
    (angularFourier_quinticCutoff_secondDerivative hε), continuous_angularInverseFourier hi.1⟩

end LpSelfSimilar.Fourier
