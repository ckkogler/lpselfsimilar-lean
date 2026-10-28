module

public import LpSelfSimilar.Fourier.AngularInverseTransform
public import LpSelfSimilar.Analysis.AffineKernelConvolution
public import Mathlib.Analysis.Fourier.FourierTransform

@[expose] public section

/-!
# The forward Fourier integral in angular frequency

The forward phase is exp(-i*x*xi), with no normalization coefficient. Its
relation to the Mathlib transform and its behavior under kernel rescaling are
proved by exact change of variables for the actual integral.
-/

open MeasureTheory MeasureTheory.Measure
open scoped FourierTransform

namespace LpSelfSimilar.Fourier

/-- The forward angular-frequency Fourier integral with the negative phase. -/
noncomputable def angularFourier (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x, angularFourierPhase (-ξ) x * f x

/-- The zero-frequency transform is exactly the integral of the function. -/
theorem angularFourier_zero (f : ℝ → ℂ) : angularFourier f 0 = ∫ x, f x := by
  simp [angularFourier, angularFourierPhase]

/-- Angular frequency equals Mathlib frequency divided by two pi. -/
theorem angularFourier_eq_mathlib_fourier (f : ℝ → ℂ) (ξ : ℝ) :
    angularFourier f ξ = (𝓕 f) (ξ / (2 * Real.pi)) := by
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold angularFourier
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have he : -2 * Real.pi * x * (ξ / (2 * Real.pi)) = (-ξ) * x := by field_simp
  change angularFourierPhase (-ξ) x * f x =
    Complex.exp ((-2 * Real.pi * x * (ξ / (2 * Real.pi)) : ℝ) * Complex.I) * f x
  rw [he]
  rfl

/-- Rescaling a kernel multiplies the actual angular frequency, with no remaining mass factor. -/
theorem angularFourier_rescaledKernel (f : ℝ → ℂ) {r : ℝ} (hr : 0 < r) (ξ : ℝ) :
    angularFourier (Analysis.rescaledKernel r f) ξ = angularFourier f (r * ξ) := by
  have he (x : ℝ) : angularFourierPhase (-ξ) x = angularFourierPhase (-(r * ξ)) (x / r) := by
    unfold angularFourierPhase
    congr 2
    field_simp
  unfold angularFourier Analysis.rescaledKernel
  simp_rw [he, mul_smul_comm]
  rw [integral_smul,
    integral_comp_div (fun x => angularFourierPhase (-(r * ξ)) x * f x) r,
    abs_of_pos hr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

end LpSelfSimilar.Fourier
