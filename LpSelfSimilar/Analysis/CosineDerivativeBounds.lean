module

public import LpSelfSimilar.Analysis.ProductDerivativeBounds
public import LpSelfSimilar.Analysis.CosineGaussianBound
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# Exact derivative costs for cosine products

On an arc where cosine is at least one eighth, each of the first two derivatives
costs at most eight times its frequency. Combining this with the finite-product
Leibniz bound preserves the square of the total cost in order two.
-/

open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- A scaled cosine has derivative cost `8*q` through order two on the positive arc. -/
theorem norm_iteratedDeriv_cos_scale_le {q x : ℝ} (hq : 0 ≤ q)
    (hc : (1 / 8 : ℝ) ≤ Real.cos (q * x)) (k : ℕ) (hk : k ≤ 2) :
    ‖iteratedDeriv k (fun y : ℝ ↦ (Real.cos (q * y) : ℂ)) x‖ ≤
      (8 * q) ^ k * Real.cos (q * x) := by
  have hc0 : 0 ≤ Real.cos (q * x) := by linarith
  have hd1 : deriv (fun y : ℝ ↦ (Real.cos (q * y) : ℂ)) =
      fun y ↦ ((-Real.sin (q * y) * q : ℝ) : ℂ) := by
    funext y
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id y).const_mul q).cos).ofReal_comp.deriv
  have hd2 : deriv (fun y : ℝ ↦ ((-Real.sin (q * y) * q : ℝ) : ℂ)) x =
      ((-(Real.cos (q * x) * q) * q : ℝ) : ℂ) := by
    simpa only [id_eq, mul_one, Pi.neg_apply] using
      (((((hasDerivAt_id x).const_mul q).sin).neg).mul_const q).ofReal_comp.deriv
  interval_cases k
  · simp only [iteratedDeriv_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc0, pow_zero, one_mul, le_refl]
  · rw [iteratedDeriv_one, hd1]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hq,
      pow_one]
    have h1 := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one (q * x)) hq
    have h2 := mul_le_mul_of_nonneg_right hc hq
    nlinarith
  · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hd1, hd2]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg hq, abs_of_nonneg hc0]
    have h2 := mul_le_mul_of_nonneg_right hc0 (sq_nonneg q)
    norm_num only [Nat.reduceAdd]
    nlinarith

/-- The first two derivatives of a finite cosine product have the exact summed cost. -/
theorem norm_iteratedDeriv_cosine_prod_le {ι : Type*} (s : Finset ι)
    (q : ι → ℝ) (x : ℝ) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hc : ∀ i ∈ s, (1 / 8 : ℝ) ≤ Real.cos (q i * x)) (k : ℕ) (hk : k ≤ 2) :
    ‖iteratedDeriv k (fun y : ℝ ↦ ∏ i ∈ s, (Real.cos (q i * y) : ℂ)) x‖ ≤
      (8 * ∑ i ∈ s, q i) ^ k * ∏ i ∈ s, Real.cos (q i * x) := by
  have h := norm_iteratedDeriv_finset_prod_le s
    (fun i y ↦ (Real.cos (q i * y) : ℂ)) (fun i ↦ Real.cos (q i * x))
    (fun i ↦ 8 * q i) 2 x
    (fun i hi ↦ by linarith [hc i hi]) (fun i hi ↦ mul_nonneg (by norm_num) (hq i hi))
    (fun i hi ↦ (Complex.ofRealCLM.contDiff.comp
      (show ContDiff ℝ 2 (fun y : ℝ ↦ Real.cos (q i * y)) from by fun_prop)).contDiffAt)
    (fun i hi j hj ↦ norm_iteratedDeriv_cos_scale_le (hq i hi) (hc i hi) j hj) k hk
  simpa only [Finset.mul_sum] using h

end LpSelfSimilar.Analysis
