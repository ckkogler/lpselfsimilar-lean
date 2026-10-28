module

public import LpSelfSimilar.Gaussian.PolynomialKernel
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# One-sided tails of the standard Gaussian

The spatial derivative of the actual Gaussian density gives the exact first
tail moment. Comparing x with the positive lower endpoint gives the standard
Mills upper bound. Exact rational estimates at amplitude two certify the
strict error threshold 1/32 used by the binary sign decoder.
-/

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology

namespace LpSelfSimilar.Gaussian

theorem tendsto_standard_kernel_zero : Tendsto (kernel 1) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_atBot.comp
    ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg
      (by norm_num : -(1 / 2 : ℝ) < 0))
  convert h.const_mul (Real.sqrt (2 * Real.pi))⁻¹ using 1
  · ext x
    simp only [kernel, mul_one]
    congr 2 <;> ring
  · ring

/-- Exact first moment on every open upper tail. -/
theorem integral_Ioi_id_mul_standard_kernel (b : ℝ) :
    (∫ x : ℝ in Ioi b, x * kernel 1 x) = kernel 1 b := by
  have hi : Integrable (fun x : ℝ => x * kernel 1 x) := by
    simpa only [Polynomial.eval_X] using
      integrable_polynomial_mul_kernel (Polynomial.X : Polynomial ℝ) (y := 1) (by norm_num)
  have hd (x : ℝ) : HasDerivAt (fun y => -kernel 1 y) (x * kernel 1 x) x := by
    convert! (hasDerivAt_kernel_space (y := 1) (by norm_num) x).neg using 1 <;>
      simp only [div_one]; ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun x _ => hd x) hi.integrableOn tendsto_standard_kernel_zero.neg (a := b)
  simpa only [neg_zero, zero_sub, neg_neg] using h

/-- Mills' comparison in the variance-one normalization. -/
theorem integral_Ioi_standard_kernel_le {b : ℝ} (hb : 0 < b) :
    (∫ x : ℝ in Ioi b, kernel 1 x) ≤ kernel 1 b / b := by
  have hi : Integrable (fun x : ℝ => x * kernel 1 x) := by
    simpa only [Polynomial.eval_X] using
      integrable_polynomial_mul_kernel (Polynomial.X : Polynomial ℝ) (y := 1) (by norm_num)
  have h := setIntegral_mono_on (s := Ioi b)
    (integrable_kernel (y := 1) (by norm_num)).integrableOn
    (hi.div_const b).integrableOn measurableSet_Ioi (fun x hx => by
      change kernel 1 x ≤ x * kernel 1 x / b
      apply (le_div_iff₀ hb).mpr
      nlinarith [mul_le_mul_of_nonneg_right hx.le (kernel_pos (by norm_num : (0 : ℝ) < 1) x).le])
  simpa only [integral_div, integral_Ioi_id_mul_standard_kernel] using h

/-- Tail probabilities are the integrals of the existing density. -/
theorem standard_gaussian_Ioi_toReal (b : ℝ) :
    ((gaussianReal 0 1) (Ioi b)).toReal = ∫ x : ℝ in Ioi b, kernel 1 x := by
  rw [gaussianReal_apply_eq_integral _ (by norm_num : (1 : NNReal) ≠ 0)]
  have hn : 0 ≤ ∫ x : ℝ in Ioi b, gaussianPDFReal 0 1 x :=
    integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x)
  rw [ENNReal.toReal_ofReal hn]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by simp [gaussianPDFReal, kernel])

/-- A rational certificate for the decoder's boundary upper bound. -/
theorem standard_kernel_two_div_two_lt : kernel 1 2 / 2 < (1 / 32 : ℝ) := by
  have he : (7 : ℝ) < exp 2 := by
    have h := Real.sum_le_exp_of_nonneg (x := (2 : ℝ)) (by norm_num) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hen : exp (-2) < (1 / 7 : ℝ) := by
    rw [exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) he
  have hspos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hs : (12 / 5 : ℝ) < Real.sqrt (2 * Real.pi) := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * Real.pi by positivity)
    nlinarith [Real.pi_gt_three]
  have hsinv : (Real.sqrt (2 * Real.pi))⁻¹ < (5 / 12 : ℝ) := by
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 12 / 5) hs
    norm_num at h ⊢
    exact h
  have hprod := mul_lt_mul hsinv hen.le (exp_pos _) (by norm_num : (0 : ℝ) ≤ 5 / 12)
  have hk : kernel 1 2 = (Real.sqrt (2 * Real.pi))⁻¹ * exp (-2) := by
    norm_num [kernel]
  rw [hk]
  linarith

theorem standard_gaussian_tail_two_lt :
    ((gaussianReal 0 1) (Ioi 2)).toReal < (1 / 32 : ℝ) := by
  rw [standard_gaussian_Ioi_toReal]
  exact (integral_Ioi_standard_kernel_le (by norm_num : (0 : ℝ) < 2)).trans_lt
    standard_kernel_two_div_two_lt

end LpSelfSimilar.Gaussian
