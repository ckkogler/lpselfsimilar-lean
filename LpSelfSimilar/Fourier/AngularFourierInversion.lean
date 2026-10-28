module

public import LpSelfSimilar.Fourier.AngularForwardTransform
public import LpSelfSimilar.Fourier.AngularMathlibNormalization
public import LpSelfSimilar.Fourier.AngularInverseRescaling
public import Mathlib.Analysis.Fourier.Inversion

@[expose] public section

/-!
# Inversion for the actual angular Fourier integrals

The proved normalization identities cancel all 2*pi factors in a forward-inverse
pair. Integrability of the transform required by Mathlib is derived from the
actual inverse or forward angular integral, rather than assumed independently.
-/

open MeasureTheory
open scoped FourierTransform

namespace LpSelfSimilar.Fourier

/-- Composing the angular forward and inverse integrals gives the exact Mathlib pair. -/
theorem angularFourier_angularInverseFourier_eq_mathlib (f : ℝ → ℂ) (ξ : ℝ) :
    angularFourier (angularInverseFourier f) ξ = (𝓕 (𝓕⁻ f)) ξ := by
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  have he : angularInverseFourier f = Analysis.rescaledKernel (2 * Real.pi) (𝓕⁻ f) :=
    funext (angularInverseFourier_eq_mathlib_inverse f)
  rw [he, angularFourier_rescaledKernel _ (by positivity), angularFourier_eq_mathlib_fourier]
  congr 1
  field_simp

/-- Pointwise forward-inverse Fourier inversion with the source's angular normalization. -/
theorem angularFourier_angularInverseFourier {f : ℝ → ℂ}
    (hc : Continuous f) (hf : Integrable f) (hi : Integrable (angularInverseFourier f)) (ξ : ℝ) :
    angularFourier (angularInverseFourier f) ξ = f ξ := by
  rw [angularFourier_angularInverseFourier_eq_mathlib]
  exact congrFun (hc.fourier_fourierInv_eq hf (integrable_mathlib_fourier_of_angularInverse hi)) ξ

/-- The mass of the actual inverse kernel is the value of its amplitude at zero. -/
theorem integral_angularInverseFourier {f : ℝ → ℂ}
    (hc : Continuous f) (hf : Integrable f) (hi : Integrable (angularInverseFourier f)) :
    (∫ x, angularInverseFourier f x) = f 0 := by
  rw [← angularFourier_zero]
  exact angularFourier_angularInverseFourier hc hf hi 0

/-- The reverse angular composition likewise gives the exact Mathlib inverse-forward pair. -/
theorem angularInverseFourier_angularFourier_eq_mathlib (f : ℝ → ℂ) (x : ℝ) :
    angularInverseFourier (angularFourier f) x = (𝓕⁻ (𝓕 f)) x := by
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hr : 0 < (2 * Real.pi)⁻¹ := by positivity
  have he : angularFourier f = (fun ξ => (𝓕 f) ((2 * Real.pi)⁻¹ * ξ)) := by
    funext ξ
    rw [angularFourier_eq_mathlib_fourier]
    congr 1
    ring
  rw [he, angularInverseFourier_comp_mul _ hr, angularInverseFourier_eq_mathlib_inverse,
    smul_smul, inv_inv, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul]
  congr 1
  field_simp

/-- Integrability of the angular forward transform supplies Mathlib transform integrability. -/
theorem integrable_mathlib_fourier_of_angularFourier {f : ℝ → ℂ}
    (hf : Integrable (angularFourier f)) : Integrable (𝓕 f) := by
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hi := hf.comp_mul_left' (by positivity : 2 * Real.pi ≠ 0)
  have he : (𝓕 f) = (fun x => angularFourier f (2 * Real.pi * x)) := by
    funext x
    rw [angularFourier_eq_mathlib_fourier]
    congr 1
    field_simp
  rw [he]
  exact hi

/-- Pointwise inverse-forward Fourier inversion with the exact angular convention. -/
theorem angularInverseFourier_angularFourier {f : ℝ → ℂ}
    (hc : Continuous f) (hf : Integrable f) (hi : Integrable (angularFourier f)) (x : ℝ) :
    angularInverseFourier (angularFourier f) x = f x := by
  rw [angularInverseFourier_angularFourier_eq_mathlib]
  exact congrFun (hc.fourierInv_fourier_eq hf (integrable_mathlib_fourier_of_angularFourier hi)) x

end LpSelfSimilar.Fourier
