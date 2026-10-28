module

public import LpSelfSimilar.Entropy.AtomicRelativeEntropy

@[expose] public section

/-!
The log-likelihood chain rule for three absolutely continuous probability laws.

Radon–Nikodym multiplication is first transferred to the first law, where both
factors are positive and finite almost everywhere. This justifies splitting the
natural logarithm. Integrability is stated explicitly: absolute continuity alone
does not justify subtracting or adding real relative entropies.
-/

open MeasureTheory MeasureTheory.Measure InformationTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

lemma llr_chain {E : Type*} [MeasurableSpace E] {μ ν ρ : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    (hμν : μ ≪ ν) (hνρ : ν ≪ ρ) :
    llr μ ρ =ᵐ[μ] fun x ↦ llr μ ν x + llr ν ρ x := by
  filter_upwards [(hμν.trans hνρ).ae_le (Measure.rnDeriv_mul_rnDeriv hμν),
    Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_ne_top μ ν),
    hμν.ae_le (Measure.rnDeriv_pos hνρ),
    (hμν.trans hνρ).ae_le (Measure.rnDeriv_ne_top ν ρ)] with x he h1 h2 h3 h4
  simp only [Pi.mul_apply] at he
  simp only [llr, ← he, ENNReal.toReal_mul]
  exact Real.log_mul (ENNReal.toReal_ne_zero.mpr ⟨h1.ne', h2⟩)
    (ENNReal.toReal_ne_zero.mpr ⟨h3.ne', h4⟩)

lemma klDiv_chain_ne_top {E : Type*} [MeasurableSpace E] {μ ν ρ : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
    (hμν : klDiv μ ν ≠ ∞) (hνρ : ν ≪ ρ) (h_int : Integrable (llr ν ρ) μ) :
    klDiv μ ρ ≠ ∞ := by
  obtain ⟨h_ac, h_int'⟩ := klDiv_ne_top_iff.mp hμν
  apply klDiv_ne_top (h_ac.trans hνρ)
  exact (h_int'.add h_int).congr (llr_chain h_ac hνρ).symm

/-- The real KL chain identity, with its integrability obligation exposed. -/
theorem toReal_klDiv_chain {E : Type*} [MeasurableSpace E] {μ ν ρ : Measure E}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    (hμν : klDiv μ ν ≠ ∞) (hνρ : ν ≪ ρ) (h_int : Integrable (llr ν ρ) μ) :
    (klDiv μ ρ).toReal = (klDiv μ ν).toReal + ∫ x, llr ν ρ x ∂μ := by
  obtain ⟨h_ac, h_int'⟩ := klDiv_ne_top_iff.mp hμν
  rw [toReal_klDiv_of_measure_eq (h_ac.trans hνρ) (by simp),
    toReal_klDiv_of_measure_eq h_ac (by simp),
    integral_congr_ae (llr_chain h_ac hνρ), integral_add h_int' h_int]

end LpSelfSimilar.Entropy
