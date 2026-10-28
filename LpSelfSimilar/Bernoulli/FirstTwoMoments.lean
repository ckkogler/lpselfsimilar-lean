module

public import LpSelfSimilar.Bernoulli.StationaryMomentIntegrals
public import LpSelfSimilar.Bernoulli.VarianceNormalizedCoefficients
public import LpSelfSimilar.Probability.AffineMomentIntegrals
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Exact first and second moments of the infinite Bernoulli law

The stationary first-moment equation is m=theta*m, hence m=0.
The two affine second moments cancel their linear terms, yielding
m2=theta^2*m2+1. All moments are integrable by the geometric support
bound, so these identities hold for the actual probability measure.
-/

open MeasureTheory
open LpSelfSimilar.Probability

namespace LpSelfSimilar.Bernoulli

/-- The actual contracting Bernoulli convolution is centered. -/
theorem integral_id_convolution_eq_zero {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (∫ x : ℝ, x ∂convolution θ) = 0 := by
  have hi := integrable_id_convolution hθ0 hθ1
  have hθ : |θ| < 1 := by rwa [abs_of_nonneg hθ0]
  have hp := integrable_affine_of_integrable_id (convolution θ) hi θ 1
  have hm : Integrable (fun x : ℝ => θ * x - 1) (convolution θ) := by
    simpa only [sub_eq_add_neg] using integrable_affine_of_integrable_id (convolution θ) hi θ (-1)
  have h := integral_convolution_stationary hθ (f := fun x : ℝ => x) (by fun_prop) hp hm
  simp only [sub_eq_add_neg] at h
  rw [integral_affine_of_integrable_id (convolution θ) hi θ 1,
    integral_affine_of_integrable_id (convolution θ) hi θ (-1)] at h
  have hz : (1 - θ) * (∫ x : ℝ, x ∂convolution θ) = 0 := by nlinarith
  exact (mul_eq_zero.mp hz).resolve_left (sub_pos.mpr hθ1).ne'

/-- The second moment of the actual Bernoulli convolution is the exact inverse variance scale. -/
theorem integral_sq_convolution_eq_inverse_variance_scale {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (∫ x : ℝ, x ^ 2 ∂convolution θ) = (1 - θ ^ 2)⁻¹ := by
  have hi := integrable_id_convolution hθ0 hθ1
  have hi2 := integrable_sq_convolution hθ0 hθ1
  have hθ : |θ| < 1 := by rwa [abs_of_nonneg hθ0]
  have hp := integrable_sq_affine_of_moments (convolution θ) hi hi2 θ 1
  have hm : Integrable (fun x : ℝ => (θ * x - 1) ^ 2) (convolution θ) := by
    simpa only [sub_eq_add_neg] using integrable_sq_affine_of_moments (convolution θ) hi hi2 θ (-1)
  have h := integral_convolution_stationary hθ (f := fun x : ℝ => x ^ 2) (by fun_prop) hp hm
  simp only [sub_eq_add_neg] at h
  rw [integral_sq_affine_of_moments (convolution θ) hi hi2 θ 1,
    integral_sq_affine_of_moments (convolution θ) hi hi2 θ (-1)] at h
  have hτ := variance_scale_pos hθ0 hθ1
  rw [← one_div]
  apply (eq_div_iff hτ.ne').mpr
  nlinarith

/-- Mathlib's actual variance of the Bernoulli law equals the inverse variance scale. -/
theorem variance_id_convolution {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ProbabilityTheory.variance id (convolution θ) = (1 - θ ^ 2)⁻¹ := by
  rw [ProbabilityTheory.variance_eq_sub (memLp_id_convolution hθ0 hθ1 2)]
  change (∫ x : ℝ, x ^ 2 ∂convolution θ) - (∫ x : ℝ, x ∂convolution θ) ^ 2 = _
  rw [integral_id_convolution_eq_zero hθ0 hθ1, integral_sq_convolution_eq_inverse_variance_scale hθ0 hθ1]
  ring

end LpSelfSimilar.Bernoulli
