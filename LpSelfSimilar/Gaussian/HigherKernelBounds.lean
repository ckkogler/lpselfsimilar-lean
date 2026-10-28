module

public import LpSelfSimilar.Gaussian.HigherDerivatives
public import LpSelfSimilar.Gaussian.PolynomialBounds
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-!
Integrability, spatial continuity and exact L1 scaling of every Gaussian variance
derivative. The uniform bound on all variances above a positive lower cutoff is
proved from the explicit polynomial kernel, for use under finite measures.
-/

open MeasureTheory Real Polynomial

namespace LpSelfSimilar.Gaussian

@[fun_prop] lemma continuous_higherKernel_space (k : ℕ) (y : ℝ) : Continuous (higherKernel k y) := by
  unfold higherKernel
  exact (continuous_const.mul ((variancePolynomial k).continuous.comp
    (continuous_id.div_const _))).mul (continuous_kernel y)

lemma integrable_higherKernel (k : ℕ) {y : ℝ} (hy : 0 < y) :
    Integrable (higherKernel k y) volume := by
  let P := (variancePolynomial k).comp (C (Real.sqrt y)⁻¹ * X)
  have hi := (integrable_polynomial_mul_kernel P hy).const_mul (y ^ (-(k : ℝ)))
  convert hi using 1
  ext x
  simp only [P, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, higherKernel]
  rw [show x / Real.sqrt y = (Real.sqrt y)⁻¹ * x by ring]
  ring

lemma higherKernel_scale (k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    higherKernel k y x = y ^ (-(k : ℝ)) / Real.sqrt y *
      higherKernel k 1 (x / Real.sqrt y) := by
  unfold higherKernel
  rw [kernel_scale hy]
  simp only [Real.one_rpow, Real.sqrt_one, div_one, one_mul]
  ring

noncomputable def higherKernelNorm (k : ℕ) : ℝ := ∫ x, |higherKernel k 1 x|

lemma higherKernelNorm_nonneg (k : ℕ) : 0 ≤ higherKernelNorm k :=
  integral_nonneg (fun _ ↦ abs_nonneg _)

lemma integral_abs_higherKernel (k : ℕ) {y : ℝ} (hy : 0 < y) :
    (∫ x, |higherKernel k y x|) = y ^ (-(k : ℝ)) * higherKernelNorm k := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hc : 0 < y ^ (-(k : ℝ)) / Real.sqrt y := by positivity
  simp_rw [higherKernel_scale k hy, abs_mul, abs_of_pos hc]
  rw [integral_const_mul, Measure.integral_comp_div (fun x ↦ |higherKernel k 1 x|),
    abs_of_pos hs, smul_eq_mul]
  unfold higherKernelNorm
  field_simp

lemma exists_bound_higherKernel_one (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |higherKernel k 1 x| ≤ C := by
  simpa only [higherKernel, Real.one_rpow, Real.sqrt_one, div_one, one_mul] using
    exists_bound_polynomial_mul_kernel_one (variancePolynomial k)

lemma exists_uniform_bound_higherKernel (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, a ≤ y → ∀ x, |higherKernel k y x| ≤ C := by
  obtain ⟨D, hD, hb⟩ := exists_bound_higherKernel_one k
  refine ⟨a ^ (-(k : ℝ)) / Real.sqrt a * D, by positivity, fun y hay x ↦ ?_⟩
  have hy : 0 < y := ha.trans_le hay
  have hpow : y ^ (-(k : ℝ)) ≤ a ^ (-(k : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ha hay (neg_nonpos.mpr (Nat.cast_nonneg k))
  have hscale : y ^ (-(k : ℝ)) / Real.sqrt y ≤ a ^ (-(k : ℝ)) / Real.sqrt a :=
    div_le_div₀ (by positivity) hpow (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt hay)
  rw [higherKernel_scale k hy, abs_mul, abs_of_pos (by positivity : 0 < y ^ (-(k : ℝ)) / Real.sqrt y)]
  exact mul_le_mul hscale (hb _) (abs_nonneg _) (by positivity)

end LpSelfSimilar.Gaussian
