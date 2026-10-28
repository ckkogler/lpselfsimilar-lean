module

public import LpSelfSimilar.WeakReverseHolder.Theorem
public import LpSelfSimilar.Analysis.AbsoluteContinuity

@[expose] public section

/-!
The measure formulation of Lemma 2.1, obtained by applying the original
function theorem to the canonical real Radon–Nikodym density. This bridge
allows stationary measures to use the verified analytic result directly.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

lemma smallSetHypothesis_density {d : ℕ} {ν : Measure (Space d)} [IsFiniteMeasure ν]
    (hac : ν ≪ volume) {ε η : ℝ} (hη : 0 ≤ η)
    (hsmall : MeasureSmallSetHypothesis ν ε η) :
    SmallSetHypothesis (density ν volume) ε η := by
  have hmass (E : Set (Space d)) : (∫ x in E, density ν volume x) = ν.real E := by
    simpa only [density, Measure.withDensity_rnDeriv_eq ν volume hac] using
      Measure.setIntegral_toReal_rnDeriv_eq_withDensity (μ := ν) (ν := volume) E
  intro x r hr hr1 E hE hsub hvol
  rw [hmass E, hmass (ball x (2 * r))]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν (ball x (2 * r)))).ne
    (hsmall x r hr hr1 E hE hsub hvol)
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hη] using h

/-- Lemma 2.1 for an absolutely continuous finite measure, with the same exact exponent. -/
theorem weak_reverse_holder_measure {d : ℕ} (hd : 1 ≤ d)
    {ν : Measure (Space d)} [IsFiniteMeasure ν] (hac : ν ≪ volume)
    {ε η : ℝ} (hε : ε ∈ Ioo 0 1) (hη : η ∈ Ioo 0 (coveringConstant d)⁻¹)
    (hsmall : MeasureSmallSetHypothesis ν ε η) :
    1 < lemmaExponent d ε η ∧
      MemLp (density ν volume) (ENNReal.ofReal (lemmaExponent d ε η)) volume :=
  weak_reverse_holder hd (density_nonneg ν volume) (integrable_density ν volume)
    hε hη (smallSetHypothesis_density hac hη.1.le hsmall)

end LpSelfSimilar
