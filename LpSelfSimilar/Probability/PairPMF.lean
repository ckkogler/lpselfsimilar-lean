module

public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

/-!
The joint PMF of two independent finite random inputs.

It is defined by the actual product probability measure. This gives both the
pointwise product of atom masses and its measure identity without postulating
independence or normalization. It complements the indexed `productPMF` API.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal

namespace LpSelfSimilar

noncomputable def pairPMF {ι κ : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] (p : PMF ι) (q : PMF κ) :
    PMF (ι × κ) := (p.toMeasure.prod q.toMeasure).toPMF

@[simp] lemma pairPMF_toMeasure {ι κ : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] (p : PMF ι) (q : PMF κ) :
    (pairPMF p q).toMeasure = p.toMeasure.prod q.toMeasure :=
  Measure.toPMF_toMeasure _

lemma pairPMF_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ] (p : PMF ι) (q : PMF κ)
    (i : ι) (j : κ) : pairPMF p q (i, j) = p i * q j := by
  change (p.toMeasure.prod q.toMeasure) {(i, j)} = _
  rw [← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton p i (measurableSet_singleton i),
    PMF.toMeasure_apply_singleton q j (measurableSet_singleton j)]

end LpSelfSimilar
