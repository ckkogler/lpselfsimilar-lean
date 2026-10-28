module

public import LpSelfSimilar.Gaussian.Moments
public import LpSelfSimilar.Gaussian.PolynomialKernel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
The explicit normalization in the revised paper's Section 3. The first variance
derivative changes sign precisely at the two standard deviations. Integrating its
negative part on that interval computes its L1 norm without an improper integral.
This keeps the original integral definition of `detailNormalization` unchanged.
-/

open MeasureTheory Real Set

namespace LpSelfSimilar.Gaussian

/-- A spatial primitive of the variance derivative at variance one. -/
lemma hasDerivAt_firstKernel_primitive (x : ℝ) :
    HasDerivAt (fun t ↦ -t / 2 * kernel 1 t) (firstKernel 1 x) x := by
  convert (((hasDerivAt_id x).neg.div_const 2).mul
    (hasDerivAt_kernel_space (by norm_num : (0 : ℝ) < 1) x)) using 1 <;> try rfl
  simp only [firstKernel, one_pow, mul_one, div_one, Pi.neg_apply, id_eq]
  ring

lemma integral_firstKernel_unit_interval :
    (∫ x in Icc (-1 : ℝ) 1, firstKernel 1 x) = -kernel 1 1 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ ↦ hasDerivAt_firstKernel_primitive x)
    ((continuous_firstKernel 1).intervalIntegrable _ _)]
  have he : kernel 1 (-1) = kernel 1 1 := by norm_num [kernel]
  rw [he]
  ring

/-- The absolute integral is twice the Gaussian density at one standard deviation. -/
lemma firstNorm_eq_twice_kernel_one : firstNorm = 2 * kernel 1 1 := by
  have hpoint (x : ℝ) : |firstKernel 1 x| =
      firstKernel 1 x - 2 * (Icc (-1 : ℝ) 1).indicator (firstKernel 1) x := by
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · rw [indicator_of_mem hx]
      have hs : x ^ 2 ≤ 1 := by
        have := mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)
        nlinarith
      have hf : firstKernel 1 x ≤ 0 := by
        unfold firstKernel
        exact mul_nonpos_of_nonpos_of_nonneg
          (div_nonpos_of_nonpos_of_nonneg (by simpa using sub_nonpos.mpr hs) (by positivity))
          (kernel_pos (by norm_num) x).le
      rw [abs_of_nonpos hf]
      ring
    · rw [indicator_of_notMem hx, mul_zero, sub_zero]
      have hs : 1 ≤ x ^ 2 := by
        simp only [mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx <;> nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1)]
      apply abs_of_nonneg
      unfold firstKernel
      exact mul_nonneg
        (div_nonneg (by simpa using sub_nonneg.mpr hs) (by positivity))
        (kernel_pos (by norm_num) x).le
  have hi := integrable_firstKernel (by norm_num : (0 : ℝ) < 1)
  unfold firstNorm
  simp_rw [hpoint]
  rw [integral_sub hi ((hi.indicator measurableSet_Icc).const_mul 2),
    integral_const_mul, integral_indicator measurableSet_Icc,
    integral_firstKernel (by norm_num), integral_firstKernel_unit_interval]
  ring

lemma firstNorm_sq_mul_pi_exp_one : firstNorm ^ 2 * (Real.pi * Real.exp 1) = 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hs0 : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  have he : Real.exp (-(1 : ℝ) / 2) ^ 2 * Real.exp 1 = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    norm_num
  rw [firstNorm_eq_twice_kernel_one]
  norm_num only [kernel, one_pow, mul_one]
  field_simp
  nlinarith [he]

/-- The exact closed form of the paper's normalization, for the original L1 definition. -/
theorem detailNormalization_eq_sqrt :
    detailNormalization = Real.sqrt (Real.pi * Real.exp 1 / 2) := by
  have hq : detailNormalization ^ 2 = Real.pi * Real.exp 1 / 2 := by
    unfold detailNormalization
    have hf := firstNorm_sq_mul_pi_exp_one
    field_simp [firstNorm_pos.ne']
    nlinarith
  have hs := Real.sq_sqrt (show 0 ≤ Real.pi * Real.exp 1 / 2 by positivity)
  nlinarith [detailNormalization_pos, Real.sqrt_nonneg (Real.pi * Real.exp 1 / 2)]

theorem two_lt_detailNormalization : 2 < detailNormalization := by
  rw [detailNormalization_eq_sqrt]
  apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 2)).mpr
  have hm := mul_lt_mul Real.pi_gt_three Real.exp_one_gt_d9.le
    (by norm_num : (0 : ℝ) < 2.7182818283) Real.pi_pos.le
  nlinarith

theorem detailNormalization_lt_twenty_one_div_ten : detailNormalization < 21 / 10 := by
  rw [detailNormalization_eq_sqrt]
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 21 / 10)).mpr
  have hm := mul_lt_mul Real.pi_lt_d2 Real.exp_one_lt_d9.le (Real.exp_pos 1)
    (by norm_num : (0 : ℝ) ≤ 3.15)
  nlinarith

end LpSelfSimilar.Gaussian
