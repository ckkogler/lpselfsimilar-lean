module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# The exact quadratic-weight L1 inequality on the real line

The integral of (1+x^2)^(-1) is pi. Integrating the nonnegative square
((1+x^2)*norm(f(x))-t)^2/(1+x^2), and choosing t=norm_1(f)/pi,
gives the weighted Cauchy--Schwarz bound without an auxiliary square-root
integrability argument. This is the spatial part of weighted Plancherel (B.1).
-/

open MeasureTheory

namespace LpSelfSimilar.Analysis

/-- Weighted Cauchy--Schwarz on the real line with its exact constant pi. -/
theorem sq_integral_norm_le_pi_mul_quadratic_energy
    {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Integrable f)
    (he : Integrable (fun x : ℝ => (1 + x ^ 2) * ‖f x‖ ^ 2)) :
    (∫ x, ‖f x‖) ^ 2 ≤ Real.pi * ∫ x, (1 + x ^ 2) * ‖f x‖ ^ 2 := by
  let t : ℝ := (∫ x, ‖f x‖) / Real.pi
  have hpoint (x : ℝ) :
      2 * t * ‖f x‖ ≤ (1 + x ^ 2) * ‖f x‖ ^ 2 + t ^ 2 * (1 + x ^ 2)⁻¹ := by
    have hw : 0 < 1 + x ^ 2 := by positivity
    have hh := div_nonneg (sq_nonneg ((1 + x ^ 2) * ‖f x‖ - t)) hw.le
    have hid : ((1 + x ^ 2) * ‖f x‖ - t) ^ 2 / (1 + x ^ 2) =
        (1 + x ^ 2) * ‖f x‖ ^ 2 - 2 * t * ‖f x‖ + t ^ 2 * (1 + x ^ 2)⁻¹ := by
      field_simp
      <;> ring
    rw [hid] at hh
    linarith
  have hb := integral_mono (hf.norm.const_mul (2 * t))
    (he.add (integrable_inv_one_add_sq.const_mul (t ^ 2))) hpoint
  simp only [Pi.add_apply] at hb
  rw [integral_const_mul, integral_add he (integrable_inv_one_add_sq.const_mul (t ^ 2)),
    integral_const_mul, integral_univ_inv_one_add_sq] at hb
  have hp := Real.pi_pos
  dsimp only [t] at hb
  field_simp at hb
  nlinarith

end LpSelfSimilar.Analysis
