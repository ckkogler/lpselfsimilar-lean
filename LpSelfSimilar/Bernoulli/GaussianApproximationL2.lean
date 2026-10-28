module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Bernoulli.GaussianApproximationMassBound
public import LpSelfSimilar.Analysis.PositiveAffineDensity
public import LpSelfSimilar.Analysis.GaussianConcentrationConstants
public import LpSelfSimilar.SelfSimilar.Concentration.SharpL2

@[expose] public section

/-!
# The actual Bernoulli density is L2 under its coarse Gaussian approximation

Normalize the actual law, derive its support and stationarity, and transport
the Gaussian small-set estimate. The explicit height and error satisfy exactly
the proved strict constant 12. The sharp normalized criterion gives L2 for the
Jacobian density, and positive affine transport returns L2 to the original f.
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis LpSelfSimilar.Gaussian
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

/-- The actual Bernoulli density gains L2 from its proved 2*chi Gaussian approximation. -/
theorem bernoulli_density_memLp_two_of_gaussian_error {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250) {f : ℝ → ℝ}
    (hfm : Measurable f) (hfi : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    (hrep : convolution θ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (herr : (∫ x : ℝ, |f x - kernel ((1 - θ ^ 2)⁻¹) x|) ≤ 2 * (-Real.log θ)) :
    MemLp f 2 volume := by
  let q := unitIntervalNormalization θ hθ1
  let σ := (convolution θ).map q
  let F := fun x : ℝ => q.scale⁻¹ * f (q.scale⁻¹ * (x - q.shift))
  haveI : IsProbabilityMeasure σ := LpSelfSimilar.Probability.isProbabilityMeasure_map q.measurable.aemeasurable
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hFm : Measurable F := by dsimp only [F]; fun_prop
  have hF0 (x : ℝ) : 0 ≤ F x := mul_nonneg (inv_pos.mpr q.scale_pos).le (hf0 _)
  have hFrep : σ = volume.withDensity (fun x => ENNReal.ofReal (F x)) := by
    change (convolution θ).map q = _
    rw [hrep, map_density_positiveAffine]
  have hFL2 : MemLp F 2 volume :=
    SelfSimilar.Concentration.memLp_two_of_small_set_bound hθ0 hθ1
      (one_le_gaussian_concentration_height hχ hgap) hχ
      (gaussian_concentration_budget_lt_parameter hθ0 hθ1 hgap) σ
      (unitIntervalNormalization_convolution_stationary hθ0 hθ1)
      (unitIntervalNormalization_convolution_compl_unitInterval hθ0.le hθ1)
      hFm hF0 hFrep (fun E hE =>
        unitIntervalNormalization_small_set_bound_of_gaussian_error hθ0 hθ1 hgap hfi hf0 hrep herr hE)
  exact memLp_of_positiveAffine_density q hFL2

end LpSelfSimilar.Bernoulli
