module

public import LpSelfSimilar.Gaussian.BinaryProbabilitySpace
public import LpSelfSimilar.Gaussian.BinaryLogDensity

@[expose] public section

/-!
# Testing the binary Gaussian posterior mean against observations

Fubini on the actual fair-sign/Gaussian product computes signed observation
integrals. The pointwise Bayes identity gives the identical integral with the
hyperbolic tangent under the observation law. Integrability is proved before
subtracting component integrals. Applying these identities to indicators will
identify the actual conditional expectation by its defining set integrals.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real

namespace LpSelfSimilar.Gaussian

/-- Gaussian expectations as volume integrals against the exact translated unit kernel. -/
theorem integral_gaussian_unit_eq_density (a : ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂gaussianReal a 1) = ∫ x, f x * kernel 1 (x - a) := by
  rw [gaussianReal_unit_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    simp only [ENNReal.toReal_ofReal (kernel_pos (y := 1) (by norm_num) _).le, smul_eq_mul]
    ring)

/-- Integrability transfers to the actual kernel-weighted test. -/
theorem integrable_test_mul_gaussian_unit_density (a : ℝ) {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal a 1)) :
    Integrable (fun x => f x * kernel 1 (x - a)) volume := by
  rw [gaussianReal_unit_eq_withDensity] at hf
  have h := (integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hf
  simpa only [ENNReal.toReal_ofReal (kernel_pos (y := 1) (by norm_num) _).le,
    smul_eq_mul, mul_comm] using h

/-- Fubini computes the fair sign times a measurable integrable observation test. -/
theorem integral_binaryInputSign_mul_output (u : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hp : Integrable f (gaussianReal u 1))
    (hn : Integrable f (gaussianReal (-u) 1)) :
    (∫ z, binaryInputSign z * f (binaryGaussianOutput u z) ∂binaryGaussianInput) =
      ((∫ x, f x ∂gaussianReal u 1) - ∫ x, f x ∂gaussianReal (-u) 1) / 2 := by
  have hfout := integrable_binaryGaussianLaw_of_components u hf hp hn
  rw [← binaryGaussianInput_map_output u] at hfout
  have hcomp := hfout.comp_measurable (measurable_binaryGaussianOutput u)
  have hi : Integrable (fun z => binaryInputSign z * f (binaryGaussianOutput u z))
      binaryGaussianInput := hcomp.bdd_mul (c := 1) measurable_binaryInputSign.aestronglyMeasurable
    (ae_of_all _ (fun z => by simp [binaryInputSign]))
  have hshift (a : ℝ) : (∫ x, f (a + x) ∂gaussianReal 0 1) = ∫ x, f x ∂gaussianReal a 1 := by
    have hg : gaussianReal a 1 = (gaussianReal 0 1).map (fun x : ℝ => a + x) := by
      rw [gaussianReal_map_const_add]
      simp
    rw [hg, integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [binaryGaussianInput, integral_prod _ hi, PMF.integral_eq_sum]
  simp only [Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool,
    ENNReal.toReal_inv, binaryInputSign, binaryGaussianOutput,
    Bernoulli.sign, Bool.false_eq_true, ite_false, ite_true, mul_one, mul_neg_one,
    neg_one_mul, one_mul]
  rw [integral_neg, hshift (-u), hshift u]
  norm_num <;> ring

/-- Bayes' density identity gives the same signed integral under the observation law. -/
theorem integral_tanh_mul_binaryGaussianLaw (u : ℝ) {f : ℝ → ℝ}
    (hp : Integrable f (gaussianReal u 1)) (hn : Integrable f (gaussianReal (-u) 1)) :
    (∫ x, tanh (u * x) * f x ∂binaryGaussianLaw u) =
      ((∫ x, f x ∂gaussianReal u 1) - ∫ x, f x ∂gaussianReal (-u) 1) / 2 := by
  rw [integral_binaryGaussianLaw_eq_density]
  have he (x : ℝ) : (tanh (u * x) * f x) * binaryGaussianDensity u x =
      (f x * kernel 1 (x - u) - f x * kernel 1 (x - (-u))) / 2 := by
    rw [show tanh (u * x) * f x * binaryGaussianDensity u x =
      f x * (tanh (u * x) * binaryGaussianDensity u x) by ring,
      tanh_mul_binaryGaussianDensity, sub_neg_eq_add]
    ring
  simp_rw [he]
  rw [integral_div, integral_sub (integrable_test_mul_gaussian_unit_density u hp)
    (integrable_test_mul_gaussian_unit_density (-u) hn),
    ← integral_gaussian_unit_eq_density, ← integral_gaussian_unit_eq_density]

/-- The posterior mean and the sign agree against every integrable observation test. -/
theorem integral_binaryInputSign_mul_output_eq_tanh (u : ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hp : Integrable f (gaussianReal u 1))
    (hn : Integrable f (gaussianReal (-u) 1)) :
    (∫ z, binaryInputSign z * f (binaryGaussianOutput u z) ∂binaryGaussianInput) =
      ∫ z, tanh (u * binaryGaussianOutput u z) * f (binaryGaussianOutput u z)
        ∂binaryGaussianInput := by
  have ht : Measurable (fun x : ℝ => tanh (u * x)) := by
    simpa only [add_zero] using (continuous_tanh_affine u 0).measurable
  have htest : Measurable (fun x : ℝ => tanh (u * x) * f x) := ht.mul hf
  rw [integral_binaryInputSign_mul_output u hf hp hn,
    ← integral_tanh_mul_binaryGaussianLaw u hp hn,
    ← binaryGaussianInput_map_output u,
    integral_map (measurable_binaryGaussianOutput u).aemeasurable htest.aestronglyMeasurable]

end LpSelfSimilar.Gaussian
