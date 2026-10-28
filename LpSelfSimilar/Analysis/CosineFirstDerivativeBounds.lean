module

public import LpSelfSimilar.Analysis.ProductDerivativeBounds
public import LpSelfSimilar.Analysis.CosineGaussianBound
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# First derivative bounds with exact cosine margins

Each factor has its own nonnegative value and derivative majorant. The finite
Leibniz estimate adds derivative costs. Unrestricted factors cost their
frequency; on the half-margin arc they cost twice their frequency while
retaining the cosine product. These are the prefix and tail estimates needed
when the splitting index depends on the frequency.
-/

open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- Value and derivative majorants for individual cosines give the exact finite product cost. -/
theorem norm_deriv_cosine_prod_le_of_bounds {ι : Type*} (s : Finset ι)
    (q v w : ι → ℝ) (x : ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hc : ∀ i ∈ s, |Real.cos (q i * x)| ≤ v i)
    (hs : ∀ i ∈ s, |Real.sin (q i * x)| * |q i| ≤ w i * v i) :
    ‖deriv (fun y : ℝ => ∏ i ∈ s, (Real.cos (q i * y) : ℂ)) x‖ ≤
      (∑ i ∈ s, w i) * ∏ i ∈ s, v i := by
  have hb (i : ι) (hi : i ∈ s) (k : ℕ) (hk : k ≤ 1) :
      ‖iteratedDeriv k (fun y : ℝ => (Real.cos (q i * y) : ℂ)) x‖ ≤
        w i ^ k * v i := by
    interval_cases k
    · simpa only [iteratedDeriv_zero, pow_zero, one_mul,
        Complex.norm_real, Real.norm_eq_abs] using hc i hi
    · have hd := (((hasDerivAt_id x).const_mul (q i)).cos).ofReal_comp.deriv
      simp only [id_eq, mul_one] at hd
      rw [iteratedDeriv_one, hd]
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, pow_one] using hs i hi
  have hp := norm_iteratedDeriv_finset_prod_le s
    (fun i y => (Real.cos (q i * y) : ℂ)) v w 1 x hv hw
    (fun i hi => (Complex.ofRealCLM.contDiff.comp
      (show ContDiff ℝ 1 (fun y : ℝ => Real.cos (q i * y)) from by fun_prop)).contDiffAt)
    hb 1 le_rfl
  simpa only [iteratedDeriv_one, pow_one] using hp

/-- Without angle restrictions, the first derivative costs at most the sum of frequencies. -/
theorem norm_deriv_cosine_prod_le_sum {ι : Type*} (s : Finset ι)
    (q : ι → ℝ) (x : ℝ) (hq : ∀ i ∈ s, 0 ≤ q i) :
    ‖deriv (fun y : ℝ => ∏ i ∈ s, (Real.cos (q i * y) : ℂ)) x‖ ≤ ∑ i ∈ s, q i := by
  have hp := norm_deriv_cosine_prod_le_of_bounds s q (fun _ => 1) q x
    (fun _ _ => zero_le_one) hq (fun i hi => Real.abs_cos_le_one _)
    (fun i hi => by
      rw [abs_of_nonneg (hq i hi), mul_one]
      exact mul_le_of_le_one_left (hq i hi) (Real.abs_sin_le_one _))
  simpa only [Finset.prod_const_one, mul_one] using hp

/-- On the half-margin arc, the product itself is retained with cost twice the frequency sum. -/
theorem norm_deriv_cosine_prod_le_half_margin {ι : Type*} (s : Finset ι)
    (q : ι → ℝ) (x : ℝ) (hq : ∀ i ∈ s, 0 ≤ q i)
    (hc : ∀ i ∈ s, (1 / 2 : ℝ) ≤ Real.cos (q i * x)) :
    ‖deriv (fun y : ℝ => ∏ i ∈ s, (Real.cos (q i * y) : ℂ)) x‖ ≤
      (2 * ∑ i ∈ s, q i) * ∏ i ∈ s, Real.cos (q i * x) := by
  have hv (i : ι) (hi : i ∈ s) : 0 ≤ Real.cos (q i * x) := by linarith [hc i hi]
  have hp := norm_deriv_cosine_prod_le_of_bounds s q
    (fun i => Real.cos (q i * x)) (fun i => 2 * q i) x hv
    (fun i hi => mul_nonneg (by norm_num) (hq i hi))
    (fun i hi => by rw [abs_of_nonneg (hv i hi)])
    (fun i hi => by
      rw [abs_of_nonneg (hq i hi)]
      have hb := mul_le_of_le_one_left (hq i hi) (Real.abs_sin_le_one (q i * x))
      have hm := mul_le_mul_of_nonneg_right (hc i hi) (hq i hi)
      nlinarith)
  simpa only [Finset.mul_sum] using hp

end LpSelfSimilar.Analysis
