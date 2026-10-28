module

public import LpSelfSimilar.Fourier.AngularMathlibNormalization
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

@[expose] public section

/-!
# The angular inverse of an integrable derivative

Mathlib's Fourier derivative theorem applies when the function and its actual
derivative are integrable. The proved angular normalization cancels all 2*pi
factors and changes the sign, yielding -i*x. No compact-support hypothesis is
needed, so this version also applies to Gaussian amplitudes.
-/

open MeasureTheory
open scoped FourierTransform

namespace LpSelfSimilar.Fourier

/-- Exact angular inverse derivative identity for an integrable differentiable function. -/
theorem angularInverseFourier_deriv_of_integrable {f : ℝ → ℂ}
    (hf : Integrable f) (hd : Differentiable ℝ f) (hdf : Integrable (deriv f)) (x : ℝ) :
    angularInverseFourier (deriv f) x = -Complex.I * (x : ℂ) * angularInverseFourier f x := by
  rw [angularInverseFourier_eq_mathlib_fourier, Real.fourier_deriv hf hd hdf,
    angularInverseFourier_eq_mathlib_fourier]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  <;> ring

end LpSelfSimilar.Fourier
