module

public import LpSelfSimilar.Entropy.Bounds
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

/-!
Relative entropy of an atom against its probability mass function.

The Radon–Nikodym derivative at a positive-mass atom is exactly the reciprocal
of its mass. Thus the KL divergence of the point mass is minus the natural
logarithm of that mass. This supplies a finite upper bound for each positive
input atom of a channel after applying the proved KL data-processing inequality.
Zero-weight inputs will be omitted or multiplied by zero in finite information.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InformationTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

lemma dirac_absolutelyContinuous_pmf {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) {a : α} (ha : p a ≠ 0) :
    Measure.dirac a ≪ p.toMeasure := by
  intro s hs
  by_cases hmem : a ∈ s
  · have h := measure_mono (Set.singleton_subset_iff.mpr hmem) (μ := p.toMeasure)
    rw [PMF.toMeasure_apply_singleton p a (measurableSet_singleton a), hs] at h
    exact (ha (le_zero_iff.mp h)).elim
  · simp [Measure.dirac_apply, hmem]

/-- The derivative is pinned at the atom by the equality of measures on its
singleton, so the conclusion does not depend on an arbitrary a.e. representative. -/
lemma rnDeriv_dirac_pmf_at {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) {a : α} (ha : p a ≠ 0) :
    (Measure.dirac a).rnDeriv p.toMeasure a = (p a)⁻¹ := by
  have he := Measure.withDensity_rnDeriv_eq (Measure.dirac a) p.toMeasure
    (dirac_absolutelyContinuous_pmf p ha)
  have h := congrArg (fun μ : Measure α ↦ μ {a}) he
  have hm : (Measure.dirac a).rnDeriv p.toMeasure a * p a = 1 := by
    simpa [withDensity_apply, lintegral_singleton, mul_comm,
      PMF.toMeasure_apply_singleton p a (measurableSet_singleton a)] using h
  exact ENNReal.eq_inv_of_mul_eq_one_left hm

/-- KL divergence is measured in nats, and is finite at every positive input atom. -/
theorem klDiv_dirac_pmf {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (p : PMF α) {a : α} (ha : p a ≠ 0) :
    klDiv (Measure.dirac a) p.toMeasure = ENNReal.ofReal (-Real.log (p a).toReal) := by
  rw [klDiv_of_ac_of_integrable (dirac_absolutelyContinuous_pmf p ha)
    (integrable_dirac (by finiteness))]
  simp only [integral_dirac, probReal_univ, add_sub_cancel_right,
    llr, rnDeriv_dirac_pmf_at p ha, ENNReal.toReal_inv, Real.log_inv]

end LpSelfSimilar.Entropy
