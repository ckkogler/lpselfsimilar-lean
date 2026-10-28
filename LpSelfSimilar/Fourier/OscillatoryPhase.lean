module

public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# The phase for inverse Fourier transforms in angular frequency

The convention is `exp(i*x*xi)`, with no hidden factor of `2*pi` in the phase.
Normalization by `1/(2*pi)` belongs to the inverse transform itself. These
elementary phase facts apply to arbitrary integrable complex functions.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- The positive complex phase for angular-frequency Fourier inversion. -/
noncomputable def angularFourierPhase (x ξ : ℝ) : ℂ :=
  Complex.exp ((x * ξ : ℝ) * Complex.I)

/-- The angular phase has norm one. -/
theorem norm_angularFourierPhase (x ξ : ℝ) : ‖angularFourierPhase x ξ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- Joint continuity of the inverse-transform phase. -/
theorem continuous_angularFourierPhase :
    Continuous (fun p : ℝ × ℝ ↦ angularFourierPhase p.1 p.2) := by
  unfold angularFourierPhase
  fun_prop

/-- Differentiating in the frequency variable retains the exact factor `i*x`. -/
theorem hasDerivAt_angularFourierPhase (x ξ : ℝ) :
    HasDerivAt (angularFourierPhase x) ((x : ℂ) * Complex.I * angularFourierPhase x ξ) ξ := by
  convert! ((((hasDerivAt_id ξ).const_mul x).ofReal_comp).mul_const Complex.I).cexp using 1 <;>
    simp only [angularFourierPhase, id_eq] <;> ring

/-- Multiplication by the phase preserves the pointwise norm. -/
theorem norm_angularFourierPhase_mul (x ξ : ℝ) (z : ℂ) :
    ‖angularFourierPhase x ξ * z‖ = ‖z‖ := by
  rw [norm_mul, norm_angularFourierPhase, one_mul]

/-- The oscillatory integrand is integrable whenever its amplitude is integrable. -/
theorem integrable_angularFourierPhase_mul {f : ℝ → ℂ} (hf : Integrable f) (x : ℝ) :
    Integrable (fun ξ ↦ angularFourierPhase x ξ * f ξ) := by
  apply hf.norm.mono'
  · exact ((continuous_angularFourierPhase.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  · exact ae_of_all _ (fun ξ ↦ (norm_angularFourierPhase_mul x ξ (f ξ)).le)

/-- The whole-line oscillatory integral obeys the elementary L1 amplitude bound. -/
theorem norm_integral_angularFourierPhase_mul_le (f : ℝ → ℂ) (x : ℝ) :
    ‖∫ ξ, angularFourierPhase x ξ * f ξ‖ ≤ ∫ ξ, ‖f ξ‖ := by
  simpa only [norm_angularFourierPhase_mul] using
    norm_integral_le_integral_norm (fun ξ ↦ angularFourierPhase x ξ * f ξ)

end LpSelfSimilar.Fourier
