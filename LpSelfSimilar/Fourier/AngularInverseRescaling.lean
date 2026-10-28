module

public import LpSelfSimilar.Fourier.AngularMeasureConvolution
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-!
# Translation and rescaling of the angular inverse integral

These are exact change-of-variable identities for the explicitly normalized
integral. Spatial translations preserve its L1 norm. The normalization `1/r`
in a rescaled kernel is derived from the frequency change of variables.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Fourier

/-- Multiplication by a negative phase translates the inverse kernel. -/
theorem angularInverseFourier_mul_phase (f : ℝ → ℂ) (y x : ℝ) :
    angularInverseFourier (fun ξ ↦ f ξ * angularFourierPhase (-y) ξ) x =
      angularInverseFourier f (x - y) := by
  unfold angularInverseFourier
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun ξ ↦ by
    change angularFourierPhase x ξ * (f ξ * angularFourierPhase (-y) ξ) =
      angularFourierPhase (x - y) ξ * f ξ
    rw [angularFourierPhase_sub]
    ring)

/-- Label-dependent phase factors preserve the full inverse norm integral. -/
theorem integral_norm_angularInverseFourier_mul_phase (f : ℝ → ℂ) (y : ℝ) :
    (∫ x, ‖angularInverseFourier (fun ξ ↦ f ξ * angularFourierPhase (-y) ξ) x‖) =
      ∫ x, ‖angularInverseFourier f x‖ := by
  simp_rw [angularInverseFourier_mul_phase]
  exact Analysis.integral_norm_translate_eq _ y

/-- The angular inverse of the rescaled amplitude has the exact spatial factor 1/r. -/
theorem angularInverseFourier_comp_mul (f : ℝ → ℂ) {r : ℝ} (hr : 0 < r) (x : ℝ) :
    angularInverseFourier (fun ξ ↦ f (r * ξ)) x = r⁻¹ • angularInverseFourier f (x / r) := by
  have he (ξ : ℝ) : angularFourierPhase x ξ = angularFourierPhase (x / r) (r * ξ) := by
    unfold angularFourierPhase
    congr 2
    field_simp
  unfold angularInverseFourier
  simp_rw [he]
  rw [integral_comp_mul_left (fun ξ ↦ angularFourierPhase (x / r) ξ * f ξ) r,
    abs_of_pos (inv_pos.mpr hr), smul_comm]

/-- Rescaling the amplitude leaves the inverse kernel's L1 norm unchanged. -/
theorem integral_norm_angularInverseFourier_comp_mul (f : ℝ → ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ x, ‖angularInverseFourier (fun ξ ↦ f (r * ξ)) x‖) =
      ∫ x, ‖angularInverseFourier f x‖ := by
  simp_rw [angularInverseFourier_comp_mul f hr, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr)]
  rw [integral_const_mul, integral_comp_div (fun x ↦ ‖angularInverseFourier f x‖) r,
    abs_of_pos hr, smul_eq_mul]
  field_simp

end LpSelfSimilar.Fourier
