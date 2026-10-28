module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Gaussian.SmoothingMeasure
public import LpSelfSimilar.Entropy.FiniteAdditiveChannel
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

@[expose] public section

/-!
# The actual binary Gaussian channel

A fair sign of amplitude `u`, plus an independent standard Gaussian, has the
explicit two-component density below. Its information is the existing finite
KL channel information. The density and likelihood identities are the analytic
starting point for the quantitative entropy input; no differential entropy or
conditional-variance formula is assumed in these definitions.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped ENNReal

namespace LpSelfSimilar.Gaussian

/-- Density of a fair sign of amplitude `u` plus standard Gaussian noise. -/
noncomputable def binaryGaussianDensity (u x : ℝ) : ℝ :=
  (kernel 1 (x - u) + kernel 1 (x + u)) / 2

/-- Genuine finite-channel information in nats, including amplitude zero. -/
noncomputable def binaryGaussianInformation (u : ℝ) : ℝ :=
  Entropy.additiveInformation (PMF.uniformOfFintype Bool)
    (fun b ↦ if b then u else -u) (gaussianReal 0 1)

lemma binaryGaussianDensity_pos (u x : ℝ) : 0 < binaryGaussianDensity u x := by
  unfold binaryGaussianDensity
  exact div_pos (add_pos (kernel_pos (by norm_num) _)
    (kernel_pos (by norm_num) _)) (by norm_num)

@[fun_prop] lemma continuous_binaryGaussianDensity (u : ℝ) :
    Continuous (binaryGaussianDensity u) := by
  unfold binaryGaussianDensity
  fun_prop

lemma integrable_binaryGaussianDensity (u : ℝ) :
    Integrable (binaryGaussianDensity u) volume := by
  have hm := (integrable_kernel (y := 1) (by norm_num)).comp_sub_right u
  have hp := (integrable_kernel (y := 1) (by norm_num)).comp_sub_right (-u)
  change Integrable (fun x => (kernel 1 (x - u) + kernel 1 (x + u)) / 2) volume
  simpa only [sub_neg_eq_add, Pi.add_apply] using (hm.add hp).div_const 2

lemma integral_binaryGaussianDensity (u : ℝ) :
    (∫ x, binaryGaussianDensity u x) = 1 := by
  have hm := (integrable_kernel (y := 1) (by norm_num)).comp_sub_right u
  have hp := (integrable_kernel (y := 1) (by norm_num)).comp_sub_right (-u)
  have hp' : Integrable (fun x => kernel 1 (x + u)) volume := by
    simpa only [sub_neg_eq_add] using hp
  unfold binaryGaussianDensity
  rw [integral_div, integral_add hm hp']
  have he : (fun x => kernel 1 (x + u)) = fun x => kernel 1 (x - (-u)) := by
    funext x; simp only [sub_neg_eq_add]
  rw [he, integral_sub_right_eq_self, integral_sub_right_eq_self,
    integral_kernel (by norm_num)]
  norm_num

/-- The explicit mixture is the density of the actual independent sum law. -/
theorem binary_gaussian_convolution_eq_withDensity (u : ℝ) :
    ((PMF.uniformOfFintype Bool).toMeasure.map (fun b ↦ if b then u else -u)) ∗
        gaussianReal 0 1 =
      volume.withDensity (fun x ↦ ENNReal.ofReal (binaryGaussianDensity u x)) := by
  let μ := (PMF.uniformOfFintype Bool).toMeasure.map (fun b ↦ if b then u else -u)
  haveI : IsProbabilityMeasure μ := LpSelfSimilar.Probability.isProbabilityMeasure_map
    (measurable_of_countable (fun b : Bool ↦ if b then u else -u)).aemeasurable
  have he : smooth μ 1 = binaryGaussianDensity u := by
    funext x
    change (∫ z, kernel 1 (x - z) ∂μ) = binaryGaussianDensity u x
    rw [show μ = _ from rfl, integral_map (measurable_of_countable _).aemeasurable
      (by fun_prop), PMF.integral_eq_sum]
    norm_num [binaryGaussianDensity, Fintype.sum_bool, PMF.uniformOfFintype_apply]
    ring
  have h := convolution_gaussian_eq_withDensity μ (y := 1) (by norm_num)
  rw [he] at h
  convert! h using 1 <;> norm_num [μ]

/-- The Gaussian likelihood ratio is an exponential affine function. -/
lemma kernel_one_sub_eq (u x : ℝ) :
    kernel 1 (x - u) = kernel 1 x * exp (-(u ^ 2) / 2) * exp (u * x) := by
  simp only [kernel, mul_one]
  rw [show -(x - u) ^ 2 / 2 = -(x ^ 2) / 2 + -(u ^ 2) / 2 + u * x by ring,
    exp_add, exp_add]
  ring

/-- Factorization of the actual mixture used for its posterior and information. -/
lemma binaryGaussianDensity_eq_cosh (u x : ℝ) :
    binaryGaussianDensity u x = kernel 1 x * exp (-(u ^ 2) / 2) * cosh (u * x) := by
  rw [binaryGaussianDensity, kernel_one_sub_eq,
    show x + u = x - (-u) by ring, kernel_one_sub_eq]
  simp only [neg_sq, neg_mul, Real.cosh_eq]
  ring

lemma binaryGaussianInformation_nonneg (u : ℝ) : 0 ≤ binaryGaussianInformation u :=
  Entropy.additiveInformation_nonneg _ _ _

end LpSelfSimilar.Gaussian
