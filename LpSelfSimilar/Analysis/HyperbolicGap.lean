module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Hyperbolic and variance comparisons with the logarithmic gap

Differentiating x*cosh(x)-sinh(x) proves tanh(x)<=x for x>=0.
The exact exponential/logarithmic identities then compare the fourth-moment
ratio (1-theta^2)/(1+theta^2) with chi=-log(theta). A separate elementary
logarithm inequality bounds the variance scale by 2*chi.
-/

open Set

namespace LpSelfSimilar.Analysis

/-- The hyperbolic tangent is bounded by the identity on the nonnegative half-line. -/
theorem tanh_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  have hd (y : ℝ) : HasDerivAt (fun z => z * Real.cosh z - Real.sinh z)
      (y * Real.sinh y) y := by
    convert! ((hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)).sub
      (Real.hasDerivAt_sinh y) using 1 <;> simp only [id_eq] <;> ring
  have hm : MonotoneOn (fun z => z * Real.cosh z - Real.sinh z) (Ici (0 : ℝ)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · fun_prop
    · intro y hy
      exact (hd y).hasDerivWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := interior_subset hy
      exact mul_nonneg hy0 (Real.sinh_nonneg_iff.mpr hy0)
  have h := hm (show (0 : ℝ) ∈ Ici 0 from by simp) hx hx
  simp only [zero_mul, Real.sinh_zero, sub_zero] at h
  rw [Real.tanh_eq_sinh_div_cosh]
  apply (div_le_iff₀ (Real.cosh_pos x)).mpr
  linarith

/-- The actual hyperbolic tangent of the logarithmic gap is the fourth-moment ratio. -/
theorem tanh_neg_log_eq_variance_ratio {θ : ℝ} (hθ : 0 < θ) :
    Real.tanh (-Real.log θ) = (1 - θ ^ 2) / (1 + θ ^ 2) := by
  rw [Real.tanh_neg, Real.tanh_eq_sinh_div_cosh, Real.sinh_log hθ, Real.cosh_log hθ]
  field_simp
  <;> ring

/-- The fourth-moment ratio is at most the logarithmic contraction gap. -/
theorem variance_ratio_le_neg_log {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (1 - θ ^ 2) / (1 + θ ^ 2) ≤ -Real.log θ := by
  rw [← tanh_neg_log_eq_variance_ratio hθ0]
  exact tanh_le_self_of_nonneg (neg_nonneg.mpr (Real.log_nonpos hθ0.le hθ1))

/-- The variance scale 1-theta^2 is at most twice the logarithmic gap. -/
theorem variance_scale_le_two_mul_neg_log {θ : ℝ} (hθ : 0 < θ) :
    1 - θ ^ 2 ≤ 2 * (-Real.log θ) := by
  have h := Real.log_le_sub_one_of_pos (sq_pos_of_pos hθ)
  rw [Real.log_pow] at h
  norm_num at h
  linarith

end LpSelfSimilar.Analysis
