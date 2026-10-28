module

public import LpSelfSimilar.Fourier.QuinticDetailInversion
public import LpSelfSimilar.Fourier.BoundedCharacteristicDerivatives

@[expose] public section

/-!
# Integrable detail kernels and actual characteristic amplitudes

The constant amplitude produces the detail kernel itself. Bounded probability
laws supply C2 amplitudes by the already proved moment argument, giving a direct
application to actual characteristic functions without a density assumption.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- The actual detail and curvature have the source-normalized transform identity. -/
theorem angularFourier_quinticDetail_secondDerivative {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (∫ ξ, angularFourierPhase x ξ * (quinticFourierDetailCurvature ε ξ : ℂ)) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * (quinticFourierDetail ε ξ : ℂ) := by
  have h := angularFourier_quinticDetailProduct_secondDerivative hε
    (P := fun _ ↦ 1) (P₁ := fun _ ↦ 0) (P₂ := fun _ ↦ 0)
    (fun ξ ↦ hasDerivAt_const ξ (1 : ℂ)) (fun ξ ↦ hasDerivAt_const ξ (0 : ℂ)) continuous_const x
  simpa only [quinticDetailProduct, quinticDetailProductCurvature, mul_one, mul_zero, add_zero] using h

/-- The actual detail multiplier has an integrable, continuous inverse Fourier kernel. -/
theorem integrable_continuous_angularInverseFourier_quinticDetail {ε : ℝ} (hε : 0 < ε) :
    Integrable (angularInverseFourier (fun ξ ↦ (quinticFourierDetail ε ξ : ℂ))) ∧
      Continuous (angularInverseFourier (fun ξ ↦ (quinticFourierDetail ε ξ : ℂ))) := by
  have hi : Integrable (fun ξ ↦ (quinticFourierDetail ε ξ : ℂ)) :=
    (integrable_quinticFourierDetail hε).ofReal
  have hi₂ : Integrable (fun ξ ↦ (quinticFourierDetailCurvature ε ξ : ℂ)) :=
    (integrable_quinticFourierDetailCurvature ε).ofReal
  exact ⟨integrable_angularInverseFourier_of_secondDerivative_identity hi hi₂
    (angularFourier_quinticDetail_secondDerivative hε), continuous_angularInverseFourier hi⟩

/-- Quantitative L1 bound for the inverse detail kernel, using its exact mass two. -/
theorem integral_norm_angularInverseFourier_quinticDetail_le {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100000) :
    (∫ x, ‖angularInverseFourier (fun ξ ↦ (quinticFourierDetail ε ξ : ℂ)) x‖) ≤ 1 + 16 / ε ^ 2 := by
  have hi : Integrable (fun ξ ↦ (quinticFourierDetail ε ξ : ℂ)) :=
    (integrable_quinticFourierDetail hε).ofReal
  have hi₂ : Integrable (fun ξ ↦ (quinticFourierDetailCurvature ε ξ : ℂ)) :=
    (integrable_quinticFourierDetailCurvature ε).ofReal
  have h := integral_norm_angularInverseFourier_le_of_secondDerivative_identity hi hi₂
    (angularFourier_quinticDetail_secondDerivative hε)
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  rw [integral_abs_quinticFourierDetail hε (by linarith)] at h
  have he : (∫ ξ, |quinticFourierDetailCurvature ε ξ|) =
      ∫ ξ, |deriv (deriv (quinticFourierDetail ε)) ξ| := by
    apply integral_congr_ae
    filter_upwards [ae_deriv_deriv_quinticFourierDetail hε] with ξ hξ
    rw [hξ]
  rw [he] at h
  have hb := (quinticFourierDetail_integral_bounds hε hεsmall).2.2
  rw [show 32 / ε ^ 2 = 2 * (16 / ε ^ 2) by ring] at hb
  linarith

/-- A bounded actual probability law supplies all smoothness needed in the product inverse bound. -/
theorem quinticDetail_charFun_inverse_L1_bound {ε : ℝ} (hε : 0 < ε)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {D : ℝ} (hb : ∀ᵐ y ∂μ, |y| ≤ D) :
    Integrable (quinticDetailProduct ε (charFun μ)) ∧
      Integrable (deriv (deriv (quinticDetailProduct ε (charFun μ)))) ∧
        Integrable (angularInverseFourier (quinticDetailProduct ε (charFun μ))) ∧
          (∫ x, ‖angularInverseFourier (quinticDetailProduct ε (charFun μ)) x‖) ≤
            (1 / 2) * ((∫ ξ, ‖quinticDetailProduct ε (charFun μ) ξ‖) +
              ∫ ξ, ‖deriv (deriv (quinticDetailProduct ε (charFun μ))) ξ‖) :=
  quinticDetailProduct_inverse_L1_bound hε (contDiff_charFun_of_ae_abs_le μ hb 2)

end LpSelfSimilar.Fourier
