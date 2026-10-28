module

public import LpSelfSimilar.Analysis.QuadraticWeightL1
public import LpSelfSimilar.Fourier.AngularParseval

@[expose] public section

/-!
# Weighted Plancherel with the exact angular-frequency constant

The spatial quadratic-weight estimate contributes pi. Parseval contributes
1/(2*pi) for each of the amplitude and its derivative. The proved transform
identity for the derivative identifies the second term with x times the inverse,
so the constants cancel to exactly one half, as in (B.1).
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- The weighted Plancherel L1 estimate from an actual derivative-transform identity. -/
theorem sq_integral_norm_angularInverseFourier_le_derivative_energy
    {f f₁ : ℝ → ℂ} (hc : Continuous f) (hc₁ : Continuous f₁)
    (hf : Integrable f) (hf₁ : Integrable f₁)
    (hi : Integrable (angularInverseFourier f))
    (hi₁ : Integrable (angularInverseFourier f₁))
    (hd : ∀ x : ℝ, angularInverseFourier f₁ x =
      -Complex.I * (x : ℂ) * angularInverseFourier f x) :
    (∫ x, ‖angularInverseFourier f x‖) ^ 2 ≤
      (1 / 2) * ((∫ ξ, ‖f ξ‖ ^ 2) + ∫ ξ, ‖f₁ ξ‖ ^ 2) := by
  have hn (x : ℝ) : ‖angularInverseFourier f₁ x‖ ^ 2 =
      x ^ 2 * ‖angularInverseFourier f x‖ ^ 2 := by
    rw [hd]
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hw (x : ℝ) : (1 + x ^ 2) * ‖angularInverseFourier f x‖ ^ 2 =
      ‖angularInverseFourier f x‖ ^ 2 + ‖angularInverseFourier f₁ x‖ ^ 2 := by
    rw [hn]
    ring
  have h0 := integrable_sq_norm_angularInverseFourier hf hi
  have h1 := integrable_sq_norm_angularInverseFourier hf₁ hi₁
  have he : Integrable (fun x : ℝ => (1 + x ^ 2) * ‖angularInverseFourier f x‖ ^ 2) := by
    simp_rw [hw]
    exact h0.add h1
  have hb := Analysis.sq_integral_norm_le_pi_mul_quadratic_energy hi he
  simp_rw [hw] at hb
  rw [integral_add h0 h1, integral_sq_norm_angularInverseFourier hc hf hi,
    integral_sq_norm_angularInverseFourier hc₁ hf₁ hi₁] at hb
  calc
    _ ≤ _ := hb
    _ = _ := by field_simp

end LpSelfSimilar.Fourier
