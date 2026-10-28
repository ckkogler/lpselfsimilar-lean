module

public import LpSelfSimilar.Analysis.SmallSetMass
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-! Mass-modulus bounds are unchanged by measure-preserving coordinates. -/

open MeasureTheory
open scoped ENNReal

namespace LpSelfSimilar

lemma smallSetMass_map_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) {μ : Measure X} {ρ : Measure Y} (he : MeasurePreserving e μ ρ)
    (ν : Measure X) {t b : ℝ≥0∞} (h : smallSetMass ν μ t ≤ b) :
    smallSetMass (ν.map e) ρ t ≤ b := by
  apply smallSetMass_le
  intro E hE hvol
  rw [Measure.map_apply e.measurable hE]
  apply (measure_le_smallSetMass ν μ (hE.preimage e.measurable) _).trans h
  rwa [he.measure_preimage hE.nullMeasurableSet]

end LpSelfSimilar
