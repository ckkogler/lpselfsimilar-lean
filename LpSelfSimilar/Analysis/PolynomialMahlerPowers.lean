module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Tactic

@[expose] public section

/-!
Mahler measure and substitution of a positive power of the variable.

On the unit circle, substitution of X^k traverses the circle k times. Periodicity
and the proved integrability of the logarithmic polynomial norm justify the
change of variables even when the polynomial vanishes on the circle. This gives
exact invariance of Mahler measure, with the zero polynomial handled separately.
-/

open Polynomial MeasureTheory intervalIntegral Real

namespace LpSelfSimilar

/-- Multiplicativity gives the genuine Mahler measure of every polynomial power. -/
lemma polynomial_mahlerMeasure_pow (p : ℂ[X]) (n : ℕ) :
    (p ^ n).mahlerMeasure = p.mahlerMeasure ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Polynomial.mahlerMeasure_mul, ih, pow_succ]

/-- Traversing an integrable periodic function a positive integer number of times
leaves its integral over a period unchanged after rescaling the argument. -/
lemma periodic_integral_comp_nat_mul {f : ℝ → ℝ} {T : ℝ}
    (hf : Function.Periodic f T) (hT : T ≠ 0)
    (hi : IntervalIntegrable f volume 0 T) {k : ℕ} (hk : 0 < k) :
    (∫ t in (0 : ℝ)..T, f ((k : ℝ) * t)) = ∫ t in (0 : ℝ)..T, f t := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hmul := hf.intervalIntegral_add_zsmul_eq (k : ℤ) 0
    (hf.intervalIntegrable₀ hT hi)
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast] at hmul
  rw [integral_comp_mul_left f hk0, mul_zero, hmul]
  simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hk0, one_mul]

/-- The logarithmic circle average is unchanged by a positive power substitution. -/
theorem polynomial_logMahlerMeasure_comp_X_pow (p : ℂ[X]) {k : ℕ} (hk : 0 < k) :
    (p.comp (X ^ k)).logMahlerMeasure = p.logMahlerMeasure := by
  let f : ℝ → ℝ := fun t ↦ Real.log ‖p.eval (circleMap 0 1 t)‖
  have hf : Function.Periodic f (2 * Real.pi) :=
    (periodic_circleMap 0 1).comp (fun z ↦ Real.log ‖p.eval z‖)
  have hi : IntervalIntegrable f volume 0 (2 * Real.pi) :=
    p.intervalIntegrable_mahlerMeasure
  simp only [Polynomial.logMahlerMeasure, circleAverage_def, eval_comp,
    eval_pow, eval_X, circleMap_zero_pow, one_pow]
  congr 1
  exact periodic_integral_comp_nat_mul hf (by positivity) hi hk

/-- Mahler measure is unchanged by substitution X -> X^k for k>=1. -/
theorem polynomial_mahlerMeasure_comp_X_pow (p : ℂ[X]) {k : ℕ} (hk : 0 < k) :
    (p.comp (X ^ k)).mahlerMeasure = p.mahlerMeasure := by
  have he : p.comp (X ^ k) = 0 ↔ p = 0 := Polynomial.expand_eq_zero hk
  simp only [Polynomial.mahlerMeasure, ne_eq, he,
    polynomial_logMahlerMeasure_comp_X_pow p hk]

end LpSelfSimilar
