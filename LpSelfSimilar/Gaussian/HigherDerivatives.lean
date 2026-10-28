module

public import LpSelfSimilar.Gaussian.PolynomialKernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section

/-!
All Gaussian variance derivatives, expressed by a recursive polynomial in the
normalized spatial coordinate. The recurrence is proved by differentiation;
`higherKernel k y x` is then identified with the actual kth variance derivative.
This provides an explicit analytic kernel for higher Gaussian detail.
-/

open MeasureTheory Real Polynomial Filter Set
open scoped Topology

namespace LpSelfSimilar.Gaussian

/-- The polynomial operation induced by one variance derivative. -/
noncomputable def varianceStep (b : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  C (1 / 2) * ((X ^ 2 - C (2 * b + 1)) * P - X * P.derivative)

noncomputable def variancePolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | k + 1 => varianceStep k (variancePolynomial k)

/-- Explicit kth variance derivative, for positive variance. -/
noncomputable def higherKernel (k : ℕ) (y x : ℝ) : ℝ :=
  y ^ (-(k : ℝ)) * (variancePolynomial k).eval (x / Real.sqrt y) * kernel y x

lemma hasDerivAt_scaled_polynomial_kernel (P : Polynomial ℝ) (b : ℝ)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun z ↦ z ^ (-b) * P.eval (x / Real.sqrt z) * kernel z x)
      (y ^ (-b - 1) * (varianceStep b P).eval (x / Real.sqrt y) * kernel y x) y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hsq := Real.sq_sqrt hy.le
  have ht : HasDerivAt (fun z ↦ x / Real.sqrt z) (-(x / Real.sqrt y) / (2 * y)) y := by
    have h := (hasDerivAt_const y x).div (Real.hasDerivAt_sqrt hy.ne') hs.ne'
    convert h using 1 <;> try rfl
    field_simp
    rw [hsq]
    ring
  have hp := (P.hasDerivAt (x / Real.sqrt y)).comp y ht
  have h := ((Real.hasDerivAt_rpow_const (p := -b) (Or.inl hy.ne')).mul hp).mul
    (hasDerivAt_kernel_variance hy x)
  have hpow : y ^ (-b) = y ^ (-b - 1) * y := by
    rw [← Real.rpow_add_one hy.ne']
    congr 1
    ring
  convert h using 1 <;> try rfl
  simp only [Pi.mul_apply, Function.comp_apply, varianceStep, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_pow, Polynomial.eval_X]
  rw [firstKernel, hpow]
  generalize hz : Real.sqrt y = z at *
  rw [← hsq]
  field_simp
  <;> ring

lemma hasDerivAt_higherKernel_variance (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun z ↦ higherKernel k z x) (higherKernel (k + 1) y x) y := by
  have h := hasDerivAt_scaled_polynomial_kernel (variancePolynomial k) k hy x
  convert h using 1 <;> try rfl
  unfold higherKernel
  rw [variancePolynomial]
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [show -((k : ℝ) + 1) = -(k : ℝ) - 1 by ring]

lemma higherKernel_zero (y x : ℝ) : higherKernel 0 y x = kernel y x := by
  simp [higherKernel, variancePolynomial]

/-- Identification with the genuine iterated variance derivative. -/
theorem higherKernel_eq_iteratedDeriv (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    higherKernel k y x = iteratedDeriv k (fun z ↦ kernel z x) y := by
  induction k generalizing y with
  | zero => simp only [higherKernel_zero, iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : (fun z ↦ higherKernel k z x) =ᶠ[𝓝 y]
        iteratedDeriv k (fun z ↦ kernel z x) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact ih hz
    exact (hasDerivAt_higherKernel_variance k hy x).deriv.symm.trans he.deriv_eq

end LpSelfSimilar.Gaussian
