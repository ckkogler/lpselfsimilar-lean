module

public import LpSelfSimilar.Analysis.ConvolutionAction
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

/-!
Finite mixtures of probability laws with nonnegative weights. Zero weights are
allowed. The explicit integral formula and probability normalization are proved
from measure addition and scaling, for later conditioning arguments.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace LpSelfSimilar

noncomputable def finiteMixture {I : Type*} [Fintype I]
    (w : I → ℝ≥0) (μ : I → Measure ℝ) : Measure ℝ := ∑ i, (w i : ℝ≥0∞) • μ i

instance finiteMixture_finite {I : Type*} [Fintype I] (w : I → ℝ≥0) (μ : I → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] : IsFiniteMeasure (finiteMixture w μ) := by
  constructor
  simp only [finiteMixture, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.sum_lt_top.mpr (fun i _ ↦ ENNReal.mul_lt_top (by simp) (measure_lt_top _ _))

lemma finiteMixture_isProbabilityMeasure {I : Type*} [Fintype I]
    (w : I → ℝ≥0) (hw : ∑ i, w i = 1) (μ : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] : IsProbabilityMeasure (finiteMixture w μ) := by
  constructor
  simp only [finiteMixture, Measure.finset_sum_apply, MeasurableSet.univ, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, ← ENNReal.coe_finset_sum, hw, ENNReal.coe_one]

lemma integral_finiteMixture {I : Type*} [Fintype I] (w : I → ℝ≥0) (μ : I → Measure ℝ)
    {f : ℝ → ℝ} (hf : ∀ i, Integrable f (μ i)) :
    (∫ x, f x ∂finiteMixture w μ) = ∑ i, (w i : ℝ) * ∫ x, f x ∂μ i := by
  unfold finiteMixture
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]
  · intro i _
    exact (hf i).smul_measure (by simp)

lemma averageTranslate_finiteMixture {I : Type*} [Fintype I]
    (w : I → ℝ≥0) (μ : I → Measure ℝ) [∀ i, IsFiniteMeasure (μ i)]
    {f : ℝ → ℝ} (hc : Continuous f) {C : ℝ} (hb : ∀ x, |f x| ≤ C) (x : ℝ) :
    averageTranslate (finiteMixture w μ) f x = ∑ i, (w i : ℝ) * averageTranslate (μ i) f x :=
  integral_finiteMixture w μ (fun i ↦ integrable_translate_of_bounded (μ i) hc hb x)

end LpSelfSimilar
