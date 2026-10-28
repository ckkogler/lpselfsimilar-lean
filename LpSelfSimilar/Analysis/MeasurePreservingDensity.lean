module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

@[expose] public section

/-!
Explicit density transport under a measure-preserving measurable equivalence.
No measurability assumption on the density is needed for this measure identity.
-/

open MeasureTheory
open scoped ENNReal

namespace LpSelfSimilar

lemma map_withDensity_of_measurePreserving {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y)
    {μ : Measure X} {ν : Measure Y} (he : MeasurePreserving e μ ν) (f : X → ℝ≥0∞) :
    (μ.withDensity f).map e = ν.withDensity (fun y ↦ f (e.symm y)) := by
  ext E hE
  rw [Measure.map_apply e.measurable hE,
    withDensity_apply _ (hE.preimage e.measurable), withDensity_apply _ hE]
  have h := he.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun y ↦ f (e.symm y)) E
  simpa only [e.symm_apply_apply] using h

end LpSelfSimilar
