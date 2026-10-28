module

public import LpSelfSimilar.Entropy.DensityLikelihood
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# Differential entropy and explicit Lebesgue densities

Differential entropy is the negative expectation of the logarithm of the actual
Radon--Nikodym density against Lebesgue volume. Like the underlying Bochner
integral, this real-valued definition is total. Applications therefore prove
log-density integrability separately. The lemmas below identify the canonical
definition with both usual density formulas and transfer actual integrability.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Entropy

/-- Differential entropy in nats, using the canonical Lebesgue density. -/
noncomputable def differentialEntropy (μ : Measure ℝ) : ℝ :=
  -∫ x, Real.log ((μ.rnDeriv volume x).toReal) ∂μ

/-- The canonical log-density agrees almost everywhere with any explicit density. -/
theorem log_rnDeriv_eq_log_density (μ : Measure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    (fun x => Real.log ((μ.rnDeriv volume x).toReal)) =ᵐ[μ] fun x => Real.log (f x) := by
  have hac : μ ≪ volume := by rw [hμ]; exact withDensity_absolutelyContinuous _ _
  have hr : μ.rnDeriv volume =ᵐ[volume] fun x => ENNReal.ofReal (f x) := by
    rw [hμ]
    exact Measure.rnDeriv_withDensity volume hf.ennreal_ofReal
  filter_upwards [hac.ae_le hr] with x hx
  rw [hx, ENNReal.toReal_ofReal (hf0 x)]

/-- Explicit log-density integrability proves finiteness for the canonical definition. -/
theorem integrable_log_rnDeriv_of_density (μ : Measure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hi : Integrable (fun x => Real.log (f x)) μ) :
    Integrable (fun x => Real.log ((μ.rnDeriv volume x).toReal)) μ :=
  hi.congr (log_rnDeriv_eq_log_density μ hf hf0 hμ).symm

/-- Differential entropy computed from an explicit Lebesgue density. -/
theorem differentialEntropy_eq_neg_integral_log_density (μ : Measure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    differentialEntropy μ = -∫ x, Real.log (f x) ∂μ := by
  unfold differentialEntropy
  congr 1
  exact integral_congr_ae (log_rnDeriv_eq_log_density μ hf hf0 hμ)

/-- Finiteness of log-density expectation is exactly integrability of f log f against volume. -/
theorem integrable_log_density_iff (μ : Measure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    Integrable (fun x => Real.log (f x)) μ ↔
      Integrable (fun x => f x * Real.log (f x)) volume := by
  rw [hμ, integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]

/-- The conventional negative integral of f log f equals canonical differential entropy. -/
theorem differentialEntropy_eq_neg_integral_density_mul_log (μ : Measure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    differentialEntropy μ = -∫ x, f x * Real.log (f x) := by
  rw [differentialEntropy_eq_neg_integral_log_density μ hf hf0 hμ, hμ,
    integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]

end LpSelfSimilar.Entropy
