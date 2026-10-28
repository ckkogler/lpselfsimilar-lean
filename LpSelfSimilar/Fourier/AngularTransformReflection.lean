module

public import LpSelfSimilar.Fourier.AngularInverseTransform

@[expose] public section

/-!
# Reflection of angular Fourier integrals

Lebesgue reflection moves a reflected frequency amplitude to the opposite
spatial frequency. Consequently a second-derivative transform identity is
preserved, since its spatial multiplier is the even function `-x^2`.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- Reflecting either coordinate gives the same angular phase. -/
theorem angularFourierPhase_neg (x ξ : ℝ) :
    angularFourierPhase x (-ξ) = angularFourierPhase (-x) ξ := by
  unfold angularFourierPhase
  congr 2
  ring

/-- Frequency reflection in the whole-line oscillatory integral. -/
theorem integral_angularFourierPhase_reflect (f : ℝ → ℂ) (x : ℝ) :
    (∫ ξ, angularFourierPhase x ξ * f (-ξ)) = ∫ ξ, angularFourierPhase (-x) ξ * f ξ := by
  have h := integral_neg_eq_self (fun ξ ↦ angularFourierPhase x ξ * f (-ξ)) volume
  simp only [neg_neg, angularFourierPhase_neg] at h
  exact h.symm

/-- Reflection is preserved by the normalized inverse transform. -/
theorem angularInverseFourier_reflect (f : ℝ → ℂ) (x : ℝ) :
    angularInverseFourier (fun ξ ↦ f (-ξ)) x = angularInverseFourier f (-x) := by
  unfold angularInverseFourier
  rw [integral_angularFourierPhase_reflect]

/-- Reflection preserves a proved second-derivative transform identity. -/
theorem angularFourier_secondDerivative_identity_reflect {f f₂ : ℝ → ℂ}
    (hid : ∀ x : ℝ, (∫ ξ, angularFourierPhase x ξ * f₂ ξ) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * f ξ) (x : ℝ) :
    (∫ ξ, angularFourierPhase x ξ * f₂ (-ξ)) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * f (-ξ) := by
  rw [integral_angularFourierPhase_reflect, integral_angularFourierPhase_reflect, hid (-x)]
  simp only [Complex.ofReal_neg, neg_sq]

/-- Adding two proved second-derivative transform identities. -/
theorem angularFourier_secondDerivative_identity_add {f f₂ g g₂ : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : Integrable f₂) (hg : Integrable g) (hg₂ : Integrable g₂)
    (hidf : ∀ x : ℝ, (∫ ξ, angularFourierPhase x ξ * f₂ ξ) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * f ξ)
    (hidg : ∀ x : ℝ, (∫ ξ, angularFourierPhase x ξ * g₂ ξ) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * g ξ) (x : ℝ) :
    (∫ ξ, angularFourierPhase x ξ * (f₂ ξ + g₂ ξ)) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * (f ξ + g ξ) := by
  simp_rw [mul_add]
  rw [integral_add (integrable_angularFourierPhase_mul hf₂ x) (integrable_angularFourierPhase_mul hg₂ x),
    integral_add (integrable_angularFourierPhase_mul hf x) (integrable_angularFourierPhase_mul hg x),
    hidf x, hidg x, mul_add]

end LpSelfSimilar.Fourier
