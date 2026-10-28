module

public import LpSelfSimilar.Probability.PMFMixture
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-!
Finite products of actual probability mass functions, defined through the
product probability measure. Coordinate independence and expectation formulas
therefore follow from the product-measure theorems, not from extra hypotheses.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal NNReal

namespace LpSelfSimilar

noncomputable def productPMF {I : Type*} [Fintype I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] (p : (i : I) → PMF (Ω i)) : PMF ((i : I) → Ω i) :=
  (Measure.pi (fun i ↦ (p i).toMeasure)).toPMF

@[simp] lemma productPMF_toMeasure {I : Type*} [Fintype I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] (p : (i : I) → PMF (Ω i)) :
    (productPMF p).toMeasure = Measure.pi (fun i ↦ (p i).toMeasure) :=
  Measure.toPMF_toMeasure _

lemma productPMF_apply {I : Type*} [Fintype I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] (p : (i : I) → PMF (Ω i)) (ω : (i : I) → Ω i) :
    productPMF p ω = ∏ i, p i (ω i) := by
  change (Measure.pi (fun i ↦ (p i).toMeasure)) {ω} = _
  rw [Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro i _
  exact (p i).toMeasure_apply_singleton _ (measurableSet_singleton _)

lemma productPMF_independent {I : Type*} [Fintype I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] (p : (i : I) → PMF (Ω i))
    (W : (i : I) → Ω i → ℝ) :
    iIndepFun (fun i ω ↦ W i (ω i)) (productPMF p).toMeasure := by
  rw [productPMF_toMeasure]
  exact iIndepFun_pi (fun i ↦ (measurable_of_countable (W i)).aemeasurable)

lemma productPMF_integral_coordinate {I : Type*} [Fintype I] {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] (p : (i : I) → PMF (Ω i))
    (i : I) (W : Ω i → ℝ) :
    (∫ ω, W (ω i) ∂(productPMF p).toMeasure) = ∫ x, W x ∂(p i).toMeasure := by
  rw [productPMF_toMeasure]
  rw [← integral_map (measurable_pi_apply i).aemeasurable
    (measurable_of_countable W).aestronglyMeasurable,
    (measurePreserving_eval (fun i ↦ (p i).toMeasure) i).map_eq]

end LpSelfSimilar
