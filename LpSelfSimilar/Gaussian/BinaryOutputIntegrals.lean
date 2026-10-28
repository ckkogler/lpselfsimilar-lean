module

public import LpSelfSimilar.Gaussian.BinaryChannelLaw
public import LpSelfSimilar.Gaussian.BinaryPosteriorMoments
public import LpSelfSimilar.Entropy.FiniteChannelReference

@[expose] public section

/-!
# Expectations under the actual binary Gaussian output law

The channel mixture is the half-sum of its two Gaussian component integrals.
Even tests have the same expectation under either component and under the
mixture. Applying this to the posterior residual variance connects fixed-noise
information differentiation to the already proved density integral bound.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real

namespace LpSelfSimilar.Gaussian

/-- The actual binary output expectation is the average of the two component expectations. -/
theorem integral_binaryGaussianLaw (u : ℝ) {f : ℝ → ℝ}
    (hf : Integrable f (binaryGaussianLaw u)) :
    (∫ x, f x ∂binaryGaussianLaw u) =
      ((∫ x, f x ∂gaussianReal u 1) + ∫ x, f x ∂gaussianReal (-u) 1) / 2 := by
  rw [binaryGaussianLaw_eq_channel_mixture] at hf ⊢
  rw [Entropy.integral_mixture_eq_weighted_sum _ _ hf]
  simp_rw [binary_channel_component_eq_gaussian]
  norm_num [Fintype.sum_bool, PMF.uniformOfFintype_apply]
  ring

/-- An even test cannot distinguish the two reflected components. -/
theorem integral_binaryGaussianLaw_of_even (u : ℝ) {f : ℝ → ℝ}
    (hf : Integrable f (binaryGaussianLaw u)) (hfm : Measurable f)
    (heven : ∀ x, f (-x) = f x) :
    (∫ x, f x ∂binaryGaussianLaw u) = ∫ x, f x ∂gaussianReal u 1 := by
  rw [integral_binaryGaussianLaw u hf, ← gaussianReal_map_neg (μ := u) (v := 1),
    integral_map (by fun_prop) hfm.aestronglyMeasurable]
  simp_rw [heven]
  ring

/-- The actual law integral is the integral against its explicit nonnegative density. -/
theorem integral_binaryGaussianLaw_eq_density (u : ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂binaryGaussianLaw u) = ∫ x, f x * binaryGaussianDensity u x := by
  rw [binaryGaussianLaw_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      ((continuous_binaryGaussianDensity u).measurable.ennreal_ofReal)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    change (ENNReal.ofReal (binaryGaussianDensity u x)).toReal * f x = f x * binaryGaussianDensity u x
    rw [ENNReal.toReal_ofReal (binaryGaussianDensity_pos u x).le, mul_comm])

/-- The fixed-noise residual variance is exactly the established mixture-density integral. -/
theorem integral_standard_binary_variance_eq_density (u : ℝ) :
    (∫ x, (1 - tanh (u ^ 2 + u * x) ^ 2) ∂gaussianReal 0 1) =
      ∫ x : ℝ, (1 - tanh (u * x) ^ 2) * binaryGaussianDensity u x := by
  let f := fun x : ℝ => 1 - tanh (u * x) ^ 2
  have hc : Continuous f := by
    have ht : Continuous (fun x : ℝ => tanh (u * x)) := by
      simpa only [add_zero] using continuous_tanh_affine u 0
    exact continuous_const.sub (ht.pow 2)
  have hi : Integrable f (binaryGaussianLaw u) := by
    have h := (integrable_const (1 : ℝ)).sub
      (integrable_tanh_affine_sq (binaryGaussianLaw u) u 0)
    exact h.congr (ae_of_all _ (fun x => by simp [f]))
  have heven (x : ℝ) : f (-x) = f x := by
    simp only [f, mul_neg, tanh_neg, neg_sq]
  have h := integral_binaryGaussianLaw_of_even u hi hc.measurable heven
  rw [integral_binaryGaussianLaw_eq_density] at h
  have hg : gaussianReal u 1 = (gaussianReal 0 1).map (fun x : ℝ => x + u) := by
    rw [gaussianReal_map_add_const]; simp
  rw [hg, integral_map (by fun_prop) hc.aestronglyMeasurable] at h
  rw [h]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by dsimp [f]; congr 3 <;> ring)

end LpSelfSimilar.Gaussian
