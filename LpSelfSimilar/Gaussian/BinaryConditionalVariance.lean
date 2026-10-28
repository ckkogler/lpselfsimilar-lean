module

public import LpSelfSimilar.Gaussian.BinaryConditionalExpectation
public import LpSelfSimilar.Gaussian.BinaryInformationDerivative
public import Mathlib.Probability.CondVar

@[expose] public section

/-!
# Actual conditional variance and the binary Gaussian information derivative

The conditional mean has been identified on the concrete independent product
space. Since the fair sign is square-integrable and has square one, Mathlib's
conditional-variance identity gives the posterior residual variance. Its
expectation is the already computed Gaussian density integral, proving the
written scalar information/MMSE formula and exact exponential bounds with the
actual conditional expectation and variance operators.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real

namespace LpSelfSimilar.Gaussian

/-- The actual conditional variance is one minus the squared posterior mean. -/
theorem condVar_binaryInputSign (u : ℝ) :
    condVar (binaryGaussianObservation u) binaryInputSign binaryGaussianInput =ᵐ[binaryGaussianInput]
      fun z => 1 - tanh (u * binaryGaussianOutput u z) ^ 2 := by
  have h := condVar_ae_eq_condExp_sq_sub_sq_condExp (binaryGaussianObservation_le u)
    (memLp_binaryInputSign 2)
  have hs : binaryInputSign ^ 2 = fun _ : Bool × ℝ => (1 : ℝ) := funext binaryInputSign_sq
  rw [hs, condExp_const (binaryGaussianObservation_le u) 1] at h
  filter_upwards [h, condExp_binaryInputSign u] with z hz hm
  simpa only [Pi.sub_apply, Pi.pow_apply, hm] using hz

/-- Expected actual conditional variance equals the proved output-density residual integral. -/
theorem integral_condVar_binaryInputSign_eq_density (u : ℝ) :
    (∫ z, condVar (binaryGaussianObservation u) binaryInputSign binaryGaussianInput z
      ∂binaryGaussianInput) =
      ∫ x : ℝ, (1 - tanh (u * x) ^ 2) * binaryGaussianDensity u x := by
  have ht : Measurable (fun x : ℝ => tanh (u * x)) := by
    simpa only [add_zero] using (continuous_tanh_affine u 0).measurable
  have hv : Measurable (fun x : ℝ => 1 - tanh (u * x) ^ 2) :=
    measurable_const.sub (ht.pow_const 2)
  calc
    _ = ∫ z, (1 - tanh (u * binaryGaussianOutput u z) ^ 2) ∂binaryGaussianInput :=
      integral_congr_ae (condVar_binaryInputSign u)
    _ = ∫ x, (1 - tanh (u * x) ^ 2) ∂binaryGaussianLaw u := by
      rw [← binaryGaussianInput_map_output u,
        integral_map (measurable_binaryGaussianOutput u).aemeasurable
          hv.aestronglyMeasurable]
    _ = _ := integral_binaryGaussianLaw_eq_density u _

/-- Exact expectation of the actual conditional variance as a Gaussian reciprocal-cosh integral. -/
theorem integral_condVar_binaryInputSign_eq_gaussian (u : ℝ) :
    (∫ z, condVar (binaryGaussianObservation u) binaryInputSign binaryGaussianInput z
      ∂binaryGaussianInput) =
      exp (-(u ^ 2) / 2) * ∫ x : ℝ, 1 / cosh (u * x) ∂gaussianReal 0 1 := by
  rw [integral_condVar_binaryInputSign_eq_density, integral_binary_variance_eq,
    integral_gaussian_unit_eq_density]
  simp only [sub_zero, div_eq_mul_inv, one_mul, mul_comm]

/-- The expected actual conditional variance has the exact Gaussian lower bound. -/
theorem exp_neg_sq_le_integral_condVar_binaryInputSign (u : ℝ) :
    exp (-(u ^ 2)) ≤
      ∫ z, condVar (binaryGaussianObservation u) binaryInputSign binaryGaussianInput z
        ∂binaryGaussianInput := by
  rw [integral_condVar_binaryInputSign_eq_density]
  exact exp_neg_sq_le_integral_binary_variance u

/-- Expected conditional variance of the fair sign is at most one. -/
theorem integral_condVar_binaryInputSign_le_one (u : ℝ) :
    (∫ z, condVar (binaryGaussianObservation u) binaryInputSign binaryGaussianInput z
      ∂binaryGaussianInput) ≤ 1 := by
  rw [integral_condVar_binaryInputSign_eq_density]
  exact integral_binary_variance_le_one u

/-- Scalar Gaussian information/MMSE with the actual conditional-variance operator. -/
theorem hasDerivAt_binaryGaussianInformation_condVar (u : ℝ) :
    HasDerivAt binaryGaussianInformation
      (u * ∫ z, condVar (binaryGaussianObservation u) binaryInputSign binaryGaussianInput z
        ∂binaryGaussianInput) u := by
  rw [integral_condVar_binaryInputSign_eq_density]
  exact hasDerivAt_binaryGaussianInformation u

/-- The derivative is the amplitude times expected actual conditional variance. -/
theorem deriv_binaryGaussianInformation_condVar (u : ℝ) :
    deriv binaryGaussianInformation u =
      u * ∫ z, condVar (binaryGaussianObservation u) binaryInputSign binaryGaussianInput z
        ∂binaryGaussianInput :=
  (hasDerivAt_binaryGaussianInformation_condVar u).deriv

end LpSelfSimilar.Gaussian
