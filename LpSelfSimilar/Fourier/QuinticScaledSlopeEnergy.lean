module

public import LpSelfSimilar.Fourier.QuinticCutoffSlopeEnergy

@[expose] public section

/-!
# Exact derivative energy after frequency scaling

The derivative contributes the scale twice after squaring, and the integral
contributes its inverse Jacobian. The resulting energy scales linearly.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Fourier

/-- The actual derivative of a frequency-rescaled cutoff retains its scale factor. -/
theorem deriv_quinticFourierCutoff_mul (ε r x : ℝ) :
    deriv (fun y => quinticFourierCutoff ε (r * y)) x =
      r * quinticFourierCutoffSlope ε (r * x) := by
  have h := ((hasDerivAt_quinticFourierCutoff ε (r * x)).comp x
    ((hasDerivAt_id x).const_mul r)).deriv
  simpa only [Function.comp_def, id_eq, mul_one, mul_comm] using h

/-- The squared actual rescaled derivative is integrable. -/
theorem integrable_sq_deriv_quinticFourierCutoff_mul {ε r : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : 0 < r) :
    Integrable (fun x => deriv (fun y => quinticFourierCutoff ε (r * y)) x ^ 2) := by
  simp_rw [deriv_quinticFourierCutoff_mul, mul_pow]
  exact ((integrable_sq_quinticFourierCutoffSlope hε hε1).comp_mul_left' hr.ne').const_mul (r ^ 2)

/-- The exact squared derivative integral after any positive frequency scaling. -/
theorem integral_sq_deriv_quinticFourierCutoff_mul {ε r : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hr : 0 < r) :
    (∫ x : ℝ, deriv (fun y => quinticFourierCutoff ε (r * y)) x ^ 2) =
      r * (10 / (7 * ε)) := by
  simp_rw [deriv_quinticFourierCutoff_mul, mul_pow]
  rw [integral_const_mul, integral_comp_mul_left (fun x => quinticFourierCutoffSlope ε x ^ 2) r,
    integral_sq_quinticFourierCutoffSlope hε hε1, abs_of_pos (inv_pos.mpr hr), smul_eq_mul]
  field_simp

end LpSelfSimilar.Fourier
