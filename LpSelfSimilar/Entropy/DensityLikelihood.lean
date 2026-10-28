module

public import LpSelfSimilar.Entropy.AtomicRelativeEntropy
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

@[expose] public section

/-!
# Likelihoods for explicit densities with a positive reference density

For two measures with densities f and g relative to a common sigma-finite
reference, positivity of g gives absolute continuity and the actual
Radon--Nikodym ratio f/g. Thus finite-channel KL information can be expressed
using explicit Gaussian likelihoods. Zero values of f are allowed.
-/

open MeasureTheory MeasureTheory.Measure InformationTheory

namespace LpSelfSimilar.Entropy

/-- A positive reference density dominates every density relative to the same base. -/
theorem absolutelyContinuous_of_positive_density {E : Type*} [MeasurableSpace E]
    (ζ μ ν : Measure E) {f g : E → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 < g x)
    (hμ : μ = ζ.withDensity (fun x => ENNReal.ofReal (f x)))
    (hν : ν = ζ.withDensity (fun x => ENNReal.ofReal (g x))) : μ ≪ ν := by
  rw [hμ, hν]
  exact (withDensity_absolutelyContinuous _ _).trans
    (withDensity_absolutelyContinuous' (hg.ennreal_ofReal.aemeasurable)
      (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (hg0 x)).ne')))

/-- The real Radon--Nikodym derivative equals the explicit density ratio. -/
theorem rnDeriv_toReal_eq_density_ratio {E : Type*} [MeasurableSpace E]
    (ζ μ ν : Measure E) [SigmaFinite ζ] [SigmaFinite μ]
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 < g x)
    (hμ : μ = ζ.withDensity (fun x => ENNReal.ofReal (f x)))
    (hν : ν = ζ.withDensity (fun x => ENNReal.ofReal (g x))) :
    (fun x => (μ.rnDeriv ν x).toReal) =ᵐ[μ] fun x => f x / g x := by
  have hac : μ ≪ ζ := by rw [hμ]; exact withDensity_absolutelyContinuous _ _
  have hleft : μ.rnDeriv ζ =ᵐ[ζ] fun x => ENNReal.ofReal (f x) := by
    rw [hμ]
    exact Measure.rnDeriv_withDensity ζ hf.ennreal_ofReal
  have hright := Measure.rnDeriv_withDensity_right μ ζ hg.ennreal_ofReal.aemeasurable
    (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (hg0 x)).ne'))
    (ae_of_all _ (fun _ => ENNReal.ofReal_ne_top))
  rw [← hν] at hright
  filter_upwards [hac.ae_le hright, hac.ae_le hleft] with x hr hl
  rw [hr, hl, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (hf0 x), ENNReal.toReal_ofReal (hg0 x).le]
  ring

/-- Equality of the actual log-likelihood and the logarithm of the density ratio. -/
theorem llr_eq_log_density_ratio {E : Type*} [MeasurableSpace E]
    (ζ μ ν : Measure E) [SigmaFinite ζ] [SigmaFinite μ]
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 < g x)
    (hμ : μ = ζ.withDensity (fun x => ENNReal.ofReal (f x)))
    (hν : ν = ζ.withDensity (fun x => ENNReal.ofReal (g x))) :
    llr μ ν =ᵐ[μ] fun x => Real.log (f x / g x) := by
  filter_upwards [rnDeriv_toReal_eq_density_ratio ζ μ ν hf hg hf0 hg0 hμ hν] with x hx
  exact congrArg Real.log hx

/-- For probability measures this is the explicit real KL integral. Integrability
can be established separately; the real equality follows Mathlib's total convention. -/
theorem toReal_klDiv_eq_integral_log_density_ratio {E : Type*} [MeasurableSpace E]
    (ζ μ ν : Measure E) [SigmaFinite ζ] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 < g x)
    (hμ : μ = ζ.withDensity (fun x => ENNReal.ofReal (f x)))
    (hν : ν = ζ.withDensity (fun x => ENNReal.ofReal (g x))) :
    (klDiv μ ν).toReal = ∫ x, Real.log (f x / g x) ∂μ := by
  rw [toReal_klDiv_of_measure_eq
    (absolutelyContinuous_of_positive_density ζ μ ν hg hg0 hμ hν) (by simp)]
  exact integral_congr_ae (llr_eq_log_density_ratio ζ μ ν hf hg hf0 hg0 hμ hν)

end LpSelfSimilar.Entropy
