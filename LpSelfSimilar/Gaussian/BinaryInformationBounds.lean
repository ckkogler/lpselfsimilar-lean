module

public import LpSelfSimilar.Gaussian.BinaryInformationDerivative

@[expose] public section

/-!
# Quantitative bounds for actual binary Gaussian information

The proved information derivative is bounded above by u and below by
u*exp(-u^2) on the nonnegative half-line. Monotonicity of the corresponding
antiderivative differences yields the quadratic upper bound and exact Gaussian
increment lower bound. No entropy-rate limit or assumed information theorem
enters these scalar estimates.
-/

open MeasureTheory Real Set

namespace LpSelfSimilar.Gaussian

theorem binaryGaussianInformation_zero : binaryGaussianInformation 0 = 0 := by
  rw [binaryGaussianInformation_eq_standard_integral]
  simp

theorem deriv_binaryGaussianInformation_le_self {u : ℝ} (hu : 0 ≤ u) :
    deriv binaryGaussianInformation u ≤ u := by
  rw [deriv_binaryGaussianInformation]
  exact mul_le_of_le_one_right hu (integral_binary_variance_le_one u)

/-- The actual information never exceeds the quadratic Gaussian signal-energy bound. -/
theorem binaryGaussianInformation_le_half_sq {u : ℝ} (hu : 0 ≤ u) :
    binaryGaussianInformation u ≤ u ^ 2 / 2 := by
  have hd (y : ℝ) : HasDerivAt (fun x : ℝ => x ^ 2 / 2 - binaryGaussianInformation x)
      (y - deriv binaryGaussianInformation y) y := by
    convert! (((hasDerivAt_id y).pow 2).div_const 2).sub
      (hasDerivAt_binaryGaussianInformation y).differentiableAt.hasDerivAt using 1 <;>
      simp only [id_eq] <;> ring
  have hm : MonotoneOn (fun x : ℝ => x ^ 2 / 2 - binaryGaussianInformation x) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro y hy; exact (hd y).continuousAt.continuousWithinAt
    · intro y hy; exact (hd y).hasDerivWithinAt
    · intro y hy
      exact sub_nonneg.mpr (deriv_binaryGaussianInformation_le_self (interior_subset hy))
  have h := hm (show (0 : ℝ) ∈ Ici 0 from by simp) hu hu
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, binaryGaussianInformation_zero, sub_zero] at h
  linarith

/-- Exact integrated derivative lower bound for any nonnegative amplitude interval. -/
theorem binaryGaussianInformation_increment_lower {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (exp (-(u ^ 2)) - exp (-(v ^ 2))) / 2 ≤
      binaryGaussianInformation v - binaryGaussianInformation u := by
  have hd (y : ℝ) : HasDerivAt
      (fun x : ℝ => binaryGaussianInformation x + exp (-(x ^ 2)) / 2)
      (deriv binaryGaussianInformation y - y * exp (-(y ^ 2))) y := by
    convert! (hasDerivAt_binaryGaussianInformation y).differentiableAt.hasDerivAt.add
      ((((hasDerivAt_id y).pow 2).neg.exp).div_const 2) using 1 <;>
      simp only [Pi.pow_apply, Pi.neg_apply, id_eq] <;> ring
  have hm : MonotoneOn
      (fun x : ℝ => binaryGaussianInformation x + exp (-(x ^ 2)) / 2) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro y hy; exact (hd y).continuousAt.continuousWithinAt
    · intro y hy; exact (hd y).hasDerivWithinAt
    · intro y hy
      exact sub_nonneg.mpr (mul_exp_neg_sq_le_deriv_binaryGaussianInformation (interior_subset hy))
  have h := hm hu (hu.trans huv) huv
  linarith

end LpSelfSimilar.Gaussian
