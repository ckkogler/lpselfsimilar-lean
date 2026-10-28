module

public import LpSelfSimilar.Fourier.OscillatoryPhase
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

/-!
# The inverse Fourier transform in angular frequency

The explicit normalization is `1/(2*pi)`. Basic linearity, continuity, and norm
bounds are proved for this actual integral, so later inversion estimates cannot
hide a convention-dependent numerical factor.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- The inverse Fourier integral for the forward convention `exp(-i*x*xi)`. -/
noncomputable def angularInverseFourier (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (2 * Real.pi)⁻¹ • ∫ ξ, angularFourierPhase x ξ * f ξ

/-- Continuity of the whole-line oscillatory integral for integrable amplitudes. -/
theorem continuous_integral_angularFourierPhase_mul {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fun x ↦ ∫ ξ, angularFourierPhase x ξ * f ξ) := by
  apply continuous_of_dominated
    (fun x ↦ (integrable_angularFourierPhase_mul hf x).aestronglyMeasurable)
    (fun x ↦ ae_of_all _ (fun ξ ↦ (norm_angularFourierPhase_mul x ξ (f ξ)).le)) hf.norm
  exact ae_of_all _ (fun ξ ↦
    (continuous_angularFourierPhase.comp (continuous_id.prodMk continuous_const)).mul continuous_const)

/-- The inverse Fourier integral is continuous for integrable amplitudes. -/
theorem continuous_angularInverseFourier {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (angularInverseFourier f) := by
  unfold angularInverseFourier
  exact (continuous_const (y := (2 * Real.pi)⁻¹)).smul
    (continuous_integral_angularFourierPhase_mul hf)

/-- Exact norm scaling by the inverse-transform normalization. -/
theorem norm_angularInverseFourier (f : ℝ → ℂ) (x : ℝ) :
    ‖angularInverseFourier f x‖ =
      (2 * Real.pi)⁻¹ * ‖∫ ξ, angularFourierPhase x ξ * f ξ‖ := by
  unfold angularInverseFourier
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 * Real.pi)⁻¹)]

/-- The elementary uniform bound with the explicit factor `1/(2*pi)`. -/
theorem norm_angularInverseFourier_le (f : ℝ → ℂ) (x : ℝ) :
    ‖angularInverseFourier f x‖ ≤ (2 * Real.pi)⁻¹ * ∫ ξ, ‖f ξ‖ := by
  rw [norm_angularInverseFourier]
  exact mul_le_mul_of_nonneg_left (norm_integral_angularFourierPhase_mul_le f x) (by positivity)

/-- Linearity under addition of integrable amplitudes. -/
theorem angularInverseFourier_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    angularInverseFourier (fun ξ ↦ f ξ + g ξ) x = angularInverseFourier f x + angularInverseFourier g x := by
  unfold angularInverseFourier
  simp_rw [mul_add]
  rw [integral_add (integrable_angularFourierPhase_mul hf x) (integrable_angularFourierPhase_mul hg x), smul_add]

/-- Linearity under subtraction of integrable amplitudes. -/
theorem angularInverseFourier_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    angularInverseFourier (fun ξ ↦ f ξ - g ξ) x = angularInverseFourier f x - angularInverseFourier g x := by
  unfold angularInverseFourier
  simp_rw [mul_sub]
  rw [integral_sub (integrable_angularFourierPhase_mul hf x) (integrable_angularFourierPhase_mul hg x), smul_sub]

end LpSelfSimilar.Fourier
