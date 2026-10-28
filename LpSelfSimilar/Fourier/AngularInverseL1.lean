module

public import LpSelfSimilar.Fourier.AngularInverseTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# The quadratic-weight L1 estimate for angular Fourier inversion

A proved second-derivative transform identity supplies quadratic decay. The
integral of `1/(1+x^2)` is exactly `pi`, so normalization by `1/(2*pi)` gives
the constant one half. The transform identity is an explicit reusable input;
interval integration by parts supplies it for piecewise cutoff applications.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- The transform identity yields the weighted oscillatory integral norm bound. -/
theorem one_add_sq_mul_norm_integral_angularFourierPhase_le {f f₂ : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : Integrable f₂) (x : ℝ)
    (hid : (∫ ξ, angularFourierPhase x ξ * f₂ ξ) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * f ξ) :
    (1 + x ^ 2) * ‖∫ ξ, angularFourierPhase x ξ * f ξ‖ ≤
      (∫ ξ, ‖f ξ‖) + ∫ ξ, ‖f₂ ξ‖ := by
  have he : (1 + (x : ℂ) ^ 2) * (∫ ξ, angularFourierPhase x ξ * f ξ) =
      ∫ ξ, angularFourierPhase x ξ * (f ξ - f₂ ξ) := by
    simp_rw [mul_sub]
    rw [integral_sub (integrable_angularFourierPhase_mul hf x)
      (integrable_angularFourierPhase_mul hf₂ x), hid]
    ring
  have hn : ‖1 + (x : ℂ) ^ 2‖ = 1 + x ^ 2 := by
    have hh : 1 + (x : ℂ) ^ 2 = ((1 + x ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    rw [hh, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 + x ^ 2)]
  have h := norm_integral_angularFourierPhase_mul_le (fun ξ ↦ f ξ - f₂ ξ) x
  rw [← he, norm_mul, hn] at h
  have hsum := integral_mono (hf.sub hf₂).norm (hf.norm.add hf₂.norm)
    (fun ξ ↦ norm_sub_le (f ξ) (f₂ ξ))
  simp only [Pi.add_apply] at hsum
  rw [integral_add hf.norm hf₂.norm] at hsum
  exact h.trans hsum

/-- Pointwise inverse-transform bound with the exact integrable quadratic majorant. -/
theorem norm_angularInverseFourier_le_of_secondDerivative_identity {f f₂ : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : Integrable f₂) (x : ℝ)
    (hid : (∫ ξ, angularFourierPhase x ξ * f₂ ξ) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * f ξ) :
    ‖angularInverseFourier f x‖ ≤
      (((∫ ξ, ‖f ξ‖) + ∫ ξ, ‖f₂ ξ‖) / (2 * Real.pi)) * (1 + x ^ 2)⁻¹ := by
  have h := one_add_sq_mul_norm_integral_angularFourierPhase_le hf hf₂ x hid
  have hh : ‖∫ ξ, angularFourierPhase x ξ * f ξ‖ ≤
      ((∫ ξ, ‖f ξ‖) + ∫ ξ, ‖f₂ ξ‖) / (1 + x ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 + x ^ 2)).mpr
    nlinarith
  rw [norm_angularInverseFourier]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (((∫ ξ, ‖f ξ‖) + ∫ ξ, ‖f₂ ξ‖) / (1 + x ^ 2)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

/-- The actual inverse transform is integrable under the second-derivative identity. -/
theorem integrable_angularInverseFourier_of_secondDerivative_identity {f f₂ : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : Integrable f₂)
    (hid : ∀ x : ℝ, (∫ ξ, angularFourierPhase x ξ * f₂ ξ) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * f ξ) :
    Integrable (angularInverseFourier f) := by
  apply (integrable_inv_one_add_sq.const_mul
    (((∫ ξ, ‖f ξ‖) + ∫ ξ, ‖f₂ ξ‖) / (2 * Real.pi))).mono'
    (continuous_angularInverseFourier hf).aestronglyMeasurable
  exact ae_of_all _ (fun x ↦ norm_angularInverseFourier_le_of_secondDerivative_identity hf hf₂ x (hid x))

/-- Exact factor one half in the inverse-transform L1 bound. -/
theorem integral_norm_angularInverseFourier_le_of_secondDerivative_identity {f f₂ : ℝ → ℂ}
    (hf : Integrable f) (hf₂ : Integrable f₂)
    (hid : ∀ x : ℝ, (∫ ξ, angularFourierPhase x ξ * f₂ ξ) =
      -(x : ℂ) ^ 2 * ∫ ξ, angularFourierPhase x ξ * f ξ) :
    (∫ x, ‖angularInverseFourier f x‖) ≤
      (1 / 2) * ((∫ ξ, ‖f ξ‖) + ∫ ξ, ‖f₂ ξ‖) := by
  have h := integral_mono
    (integrable_angularInverseFourier_of_secondDerivative_identity hf hf₂ hid).norm
    (integrable_inv_one_add_sq.const_mul
      (((∫ ξ, ‖f ξ‖) + ∫ ξ, ‖f₂ ξ‖) / (2 * Real.pi)))
    (fun x ↦ norm_angularInverseFourier_le_of_secondDerivative_identity hf hf₂ x (hid x))
  rw [integral_const_mul, integral_univ_inv_one_add_sq] at h
  have he : (((∫ ξ, ‖f ξ‖) + ∫ ξ, ‖f₂ ξ‖) / (2 * Real.pi)) * Real.pi =
      (1 / 2) * ((∫ ξ, ‖f ξ‖) + ∫ ξ, ‖f₂ ξ‖) := by field_simp
  exact h.trans_eq he

end LpSelfSimilar.Fourier
