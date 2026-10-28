module

public import LpSelfSimilar.Bernoulli.UnitIntervalNormalization
public import LpSelfSimilar.Bernoulli.NormalizedGaussianHeight
public import LpSelfSimilar.Analysis.ProbabilityDensityApproximation
public import LpSelfSimilar.Analysis.PositiveAffineMassBound

@[expose] public section

/-!
# The coarse small-set bound supplied by the actual Gaussian approximation

Both the actual Bernoulli density and the comparison Gaussian have integral
one. Their L1 error 2*chi therefore gives an additive set-mass error chi.
The positive affine support normalization changes only the height constant,
which the proved Gaussian peak estimate bounds by 6/(5*sqrt(chi)).
-/

open MeasureTheory Set
open LpSelfSimilar.Analysis LpSelfSimilar.Gaussian
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

/-- The original Bernoulli law inherits the Gaussian height bound and half its L1 error. -/
theorem convolution_small_set_bound_of_gaussian_error {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) {f : ℝ → ℝ}
    (hf : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    (hrep : convolution θ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (herr : (∫ x : ℝ, |f x - kernel ((1 - θ ^ 2)⁻¹) x|) ≤ 2 * (-Real.log θ))
    {E : Set ℝ} (hE : MeasurableSet E) :
    convolution θ E ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (1 - θ ^ 2)⁻¹))⁻¹) *
      volume E + ENNReal.ofReal (-Real.log θ) := by
  have ht := inv_pos.mpr (variance_scale_pos hθ0.le hθ1)
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hmass : (∫ x : ℝ, f x) = ∫ x : ℝ, kernel ((1 - θ ^ 2)⁻¹) x := by
    rw [integral_eq_one_of_probability_density volume (convolution θ) hf hf0 hrep,
      integral_kernel ht]
  exact small_set_bound_of_equal_mass_bounded_approximation hf hf0 hrep
    (integrable_kernel ht.le) hmass (by positivity) hχ.le (kernel_le_peak ht) herr hE

/-- The actual normalized law has the exact height/error input required by the sharp stopping lemma. -/
theorem unitIntervalNormalization_small_set_bound_of_gaussian_error {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250) {f : ℝ → ℝ}
    (hf : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    (hrep : convolution θ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (herr : (∫ x : ℝ, |f x - kernel ((1 - θ ^ 2)⁻¹) x|) ≤ 2 * (-Real.log θ))
    {E : Set ℝ} (hE : MeasurableSet E) :
    ((convolution θ).map (unitIntervalNormalization θ hθ1)) E ≤
      ENNReal.ofReal (6 / (5 * Real.sqrt (-Real.log θ))) * volume E + ENNReal.ofReal (-Real.log θ) := by
  let q := unitIntervalNormalization θ hθ1
  let C := (Real.sqrt (2 * Real.pi * (1 - θ ^ 2)⁻¹))⁻¹
  have ht := inv_pos.mpr (variance_scale_pos hθ0.le hθ1)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hheight : C * q.scale⁻¹ ≤ 6 / (5 * Real.sqrt (-Real.log θ)) := by
    change C * ((1 - θ) / 2)⁻¹ ≤ _
    rw [mul_comm]
    exact normalizedGaussianPeak_le_concentration_height hθ0 hθ1 hgap
  exact positiveAffine_map_small_set_bound q (convolution θ) hC hheight
    (fun _ hA => convolution_small_set_bound_of_gaussian_error hθ0 hθ1 hf hf0 hrep herr hA) hE

end LpSelfSimilar.Bernoulli
