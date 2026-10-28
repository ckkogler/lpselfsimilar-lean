module

public import LpSelfSimilar.Fourier.AngularInverseTransform
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-!
# Exact normalization between angular and Mathlib Fourier integrals

Mathlib uses frequency in cycles, with a phase containing 2*pi. The angular
inverse integral has the coefficient 1/(2*pi). These identities prove the
coordinate change explicitly and transfer integrability to the transform needed
by Mathlib's inversion theorem.
-/

open MeasureTheory
open scoped FourierTransform

namespace LpSelfSimilar.Fourier

/-- The angular inverse is the rescaled Mathlib inverse with its exact coefficient. -/
theorem angularInverseFourier_eq_mathlib_inverse (f : ℝ → ℂ) (x : ℝ) :
    angularInverseFourier f x = (2 * Real.pi)⁻¹ • (𝓕⁻ f) (x / (2 * Real.pi)) := by
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
  unfold angularInverseFourier
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro ξ
  have he : -2 * Real.pi * ξ * -(x / (2 * Real.pi)) = x * ξ := by field_simp
  change angularFourierPhase x ξ * f ξ =
    Complex.exp ((-2 * Real.pi * ξ * -(x / (2 * Real.pi)) : ℝ) * Complex.I) * f ξ
  rw [he]
  rfl

/-- Reflection expresses the angular inverse directly through Mathlib's forward transform. -/
theorem angularInverseFourier_eq_mathlib_fourier (f : ℝ → ℂ) (x : ℝ) :
    angularInverseFourier f x = (2 * Real.pi)⁻¹ • (𝓕 f) (-(x / (2 * Real.pi))) := by
  rw [angularInverseFourier_eq_mathlib_inverse, Real.fourierInv_eq_fourier_neg]

/-- Conversely, the forward Mathlib transform is an explicit rescaling of the angular inverse. -/
theorem mathlib_fourier_eq_angularInverseFourier (f : ℝ → ℂ) (x : ℝ) :
    (𝓕 f) x = (2 * Real.pi) • angularInverseFourier f (-2 * Real.pi * x) := by
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  rw [angularInverseFourier_eq_mathlib_fourier, smul_smul]
  have he : -((-2 * Real.pi * x) / (2 * Real.pi)) = x := by field_simp
  rw [he, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]

/-- Integrability of the actual angular inverse supplies the forward-transform integrability input. -/
theorem integrable_mathlib_fourier_of_angularInverse {f : ℝ → ℂ}
    (hf : Integrable (angularInverseFourier f)) : Integrable (𝓕 f) := by
  have hi := (hf.comp_mul_left' (by positivity : -2 * Real.pi ≠ 0)).smul (2 * Real.pi)
  have he : (𝓕 f) = (fun x => (2 * Real.pi) • angularInverseFourier f (-2 * Real.pi * x)) :=
    funext (mathlib_fourier_eq_angularInverseFourier f)
  rw [he]
  exact hi

end LpSelfSimilar.Fourier
