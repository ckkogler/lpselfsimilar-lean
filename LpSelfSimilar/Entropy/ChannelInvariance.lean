module

public import LpSelfSimilar.Entropy.FiniteChannelChain

@[expose] public section

/-!
Channel information is invariant under measurable changes of output coordinates
and under merging input labels that give the same conditional law.

The output statement follows by applying KL data processing in both directions.
The input statement identifies both actual mixtures, then transports the finite
weighted KL sum through the pushforward PMF. In particular, an entropy bound can
use the actual signal law even when many digit words have the same value.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InformationTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

lemma klDiv_map_measurableEquiv {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (e : E ≃ᵐ F) :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  apply le_antisymm (klDiv_map_le μ ν e.measurable)
  have h := klDiv_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [Measure.map_map e.symm.measurable e.measurable,
    e.symm_comp_self, Measure.map_id] using h

/-- Invertible output coordinates preserve information exactly. -/
theorem finiteInformation_map_measurableEquiv {ι E F : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSpace E] [MeasurableSpace F]
    (p : PMF ι) (K : Kernel ι E) [IsMarkovKernel K] (e : E ≃ᵐ F) :
    finiteInformation p (K.map e) = finiteInformation p K := by
  unfold finiteInformation
  simp only [Kernel.map_apply _ e.measurable,
    ← Measure.map_comp p.toMeasure K e.measurable, klDiv_map_measurableEquiv]

lemma finiteInformation_eq_lintegral {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace E]
    (p : PMF ι) (K : Kernel ι E) :
    finiteInformation p K = ∫⁻ i, klDiv (K i) (K ∘ₘ p.toMeasure) ∂p.toMeasure := by
  rw [lintegral_fintype]
  simp only [finiteInformation,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

/-- Relabeling the signal replaces its input PMF by the actual pushforward law. -/
theorem finiteInformation_comap_map {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] [MeasurableSpace E]
    (p : PMF ι) (K : Kernel κ E) (f : ι → κ) :
    finiteInformation p (K.comap f (measurable_of_countable f)) =
      finiteInformation (p.map f) K := by
  have hf := measurable_of_countable f
  have hm : K.comap f hf ∘ₘ p.toMeasure = K ∘ₘ (p.map f).toMeasure := by
    rw [← PMF.toMeasure_map f p hf, ← Measure.deterministic_comp_eq_map hf,
      Measure.comp_assoc, Kernel.comp_deterministic_eq_comap]
  rw [finiteInformation_eq_lintegral, finiteInformation_eq_lintegral, hm,
    ← PMF.toMeasure_map f p hf, lintegral_map (measurable_of_countable _) hf]
  rfl

end LpSelfSimilar.Entropy
