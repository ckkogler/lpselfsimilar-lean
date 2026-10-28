module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Tactic

@[expose] public section

/-!
The real Gaussian heat kernel parameterized by its variance, and its first
variance derivative. Positive-variance kernels agree with Mathlib's Gaussian
probability density. All derivative formulas below are proved from the explicit
kernel; zero/negative variances are never used in an analytic assertion.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace LpSelfSimilar.Gaussian

/-- The centered Gaussian density of variance `y`, for `y > 0`. -/
noncomputable def kernel (y x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * y))⁻¹ * Real.exp (-x ^ 2 / (2 * y))

/-- Explicit first derivative in the variance. -/
noncomputable def firstKernel (y x : ℝ) : ℝ :=
  (x ^ 2 - y) / (2 * y ^ 2) * kernel y x

lemma kernel_eq_gaussianPDFReal {y : ℝ} (hy : 0 ≤ y) (x : ℝ) :
    kernel y x = gaussianPDFReal 0 (NNReal.mk y hy) x := by
  simp [kernel, gaussianPDFReal]

lemma kernel_pos {y : ℝ} (hy : 0 < y) (x : ℝ) : 0 < kernel y x := by
  unfold kernel
  positivity

lemma integrable_kernel {y : ℝ} (hy : 0 ≤ y) : Integrable (kernel y) volume := by
  rw [show kernel y = gaussianPDFReal 0 (NNReal.mk y hy) from funext (kernel_eq_gaussianPDFReal hy)]
  exact integrable_gaussianPDFReal _ _

lemma integral_kernel {y : ℝ} (hy : 0 < y) : ∫ x, kernel y x = 1 := by
  simp_rw [kernel_eq_gaussianPDFReal hy.le]
  apply integral_gaussianPDFReal_eq_one
  intro h
  have hreal := congrArg (fun z : ℝ≥0 ↦ (z : ℝ)) h
  exact hy.ne' (by simpa using hreal)

@[fun_prop] lemma continuous_kernel (y : ℝ) : Continuous (kernel y) := by
  unfold kernel
  fun_prop

lemma kernel_le_peak {y : ℝ} (hy : 0 < y) (x : ℝ) :
    kernel y x ≤ (Real.sqrt (2 * Real.pi * y))⁻¹ := by
  unfold kernel
  have he : Real.exp (-x ^ 2 / (2 * y)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg x])
      (by positivity))
  simpa using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (Real.sqrt (2 * Real.pi * y))⁻¹)

/-- The basic variance differentiation identity defining ordinary detail. -/
lemma hasDerivAt_kernel_variance {y : ℝ} (hy : 0 < y) (x : ℝ) :
    HasDerivAt (fun t ↦ kernel t x) (firstKernel y x) y := by
  have hπ : 0 < 2 * Real.pi * y := by positivity
  have hs : Real.sqrt (2 * Real.pi * y) ≠ 0 := (Real.sqrt_pos.mpr hπ).ne'
  have h₁ := (((hasDerivAt_id y).const_mul (2 * Real.pi)).sqrt hπ.ne').inv hs
  have h₂ := ((hasDerivAt_const y (-x ^ 2)).div
    ((hasDerivAt_id y).const_mul 2) (by positivity : 2 * y ≠ 0)).exp
  convert h₁.mul h₂ using 1 <;> try rfl
  dsimp [firstKernel, kernel]
  have hsq := Real.sq_sqrt hπ.le
  have hsq' : Real.sqrt (y * 2 * Real.pi) ^ 2 = y * 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  field_simp
  nlinarith

lemma deriv_kernel_variance {y : ℝ} (hy : 0 < y) (x : ℝ) :
    deriv (fun t ↦ kernel t x) y = firstKernel y x :=
  (hasDerivAt_kernel_variance hy x).deriv

@[fun_prop] lemma continuous_firstKernel (y : ℝ) : Continuous (firstKernel y) := by
  unfold firstKernel
  fun_prop

lemma integrable_firstKernel {y : ℝ} (hy : 0 < y) : Integrable (firstKernel y) volume := by
  have hb : 0 < 1 / (2 * y) := by positivity
  have h₀ := integrable_exp_neg_mul_sq hb
  have h₂ := integrable_rpow_mul_exp_neg_mul_sq hb (s := 2) (by norm_num)
  simp only [Real.rpow_two] at h₂
  have h := (h₂.sub (h₀.const_mul y)).const_mul ((Real.sqrt (2 * Real.pi * y))⁻¹ / (2 * y ^ 2))
  convert h using 1
  ext x
  unfold firstKernel kernel
  simp only [Pi.sub_apply]
  rw [show -x ^ 2 / (2 * y) = -(1 / (2 * y)) * x ^ 2 by ring]
  ring

/-- Gaussian scaling in the variance parameter. -/
lemma kernel_scale {y : ℝ} (hy : 0 < y) (x : ℝ) :
    kernel y x = (Real.sqrt y)⁻¹ * kernel 1 (x / Real.sqrt y) := by
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hsq := Real.sq_sqrt hy.le
  have hexp : -(x / Real.sqrt y) ^ 2 / 2 = -x ^ 2 / (2 * y) := by
    rw [div_pow, hsq]
    ring
  simp only [kernel, mul_one, hexp, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi),
    mul_inv_rev]
  ring

/-- The first variance derivative has scale `y^(-3/2)`. -/
lemma firstKernel_scale {y : ℝ} (hy : 0 < y) (x : ℝ) :
    firstKernel y x = y⁻¹ * (Real.sqrt y)⁻¹ * firstKernel 1 (x / Real.sqrt y) := by
  have hs : Real.sqrt y ≠ 0 := (Real.sqrt_pos.mpr hy).ne'
  have hsq := Real.sq_sqrt hy.le
  simp only [firstKernel, one_pow, mul_one, div_pow, hsq]
  rw [kernel_scale hy]
  field_simp
  <;> ring

end LpSelfSimilar.Gaussian
