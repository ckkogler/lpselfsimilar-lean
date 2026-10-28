module

public import LpSelfSimilar.Bernoulli.Decomposition
public import LpSelfSimilar.Bernoulli.CosineDerivativeLimits
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Integrating the actual Bernoulli stationarity identity

The geometric support bound gives every moment. Integrating the proved
two-map stationarity identity reduces moments of the infinite law to
ordinary polynomial integrals. All integrability hypotheses for sums,
pushforwards and finite measure weights are discharged explicitly.
-/

open MeasureTheory
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

/-- The identity has every finite moment under the actual unscaled Bernoulli law. -/
theorem memLp_id_convolution {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (p : ℝ≥0∞) :
    MemLp id p (convolution θ) := by
  have h := memLp_id_scaled_convolution hθ0 hθ1 1 p
  have he : (fun x : ℝ => (1 : ℝ) * x) = id := by funext x; simp
  rw [he, Measure.map_id] at h
  exact h

/-- The first moment of the actual Bernoulli law is integrable. -/
theorem integrable_id_convolution {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    Integrable (fun x : ℝ => x) (convolution θ) :=
  (memLp_id_convolution hθ0 hθ1 1).integrable (by norm_num)

/-- The second moment of the actual Bernoulli law is integrable. -/
theorem integrable_sq_convolution {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    Integrable (fun x : ℝ => x ^ 2) (convolution θ) :=
  (memLp_two_iff_integrable_sq (by fun_prop)).mp (memLp_id_convolution hθ0 hθ1 2)

/-- The actual stationary measure identity integrates any admissible real function. -/
theorem integral_convolution_stationary {θ : ℝ} (hθ : |θ| < 1) {f : ℝ → ℝ}
    (hf : Measurable f)
    (hp : Integrable (fun x => f (θ * x + 1)) (convolution θ))
    (hm : Integrable (fun x => f (θ * x - 1)) (convolution θ)) :
    (∫ x : ℝ, f x ∂convolution θ) =
      (1 / 2 : ℝ) * ((∫ x : ℝ, f (θ * x + 1) ∂convolution θ) +
        ∫ x : ℝ, f (θ * x - 1) ∂convolution θ) := by
  have hip : Integrable f ((convolution θ).map (fun x => θ * x + 1)) :=
    (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).mpr hp
  have him : Integrable f ((convolution θ).map (fun x => θ * x - 1)) :=
    (integrable_map_measure hf.aestronglyMeasurable (by fun_prop)).mpr hm
  have he := congrArg (fun μ : Measure ℝ => ∫ x : ℝ, f x ∂μ) (convolution_stationary hθ)
  rw [integral_add_measure (hip.smul_measure (by norm_num)) (him.smul_measure (by norm_num)),
    integral_smul_measure, integral_smul_measure,
    integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_map (by fun_prop) hf.aestronglyMeasurable] at he
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul] at he
  convert! he using 1 <;> ring

end LpSelfSimilar.Bernoulli
