module

public import LpSelfSimilar.Probability.TotalConditioning
public import LpSelfSimilar.Probability.PMFMixture

@[expose] public section

/-!
The law of a finite conditioning statistic, indexed only by its positive-mass
values. Its mixture reconstructs the original measure, and its expected
conditional variance is exactly the finite conditional-moment formula.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace LpSelfSimilar.FiniteProbability

noncomputable def marginalSupportPMF {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) : PMF (p.map f).support := by
  classical
  letI : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  apply PMF.ofFintype (fun b : (p.map f).support ↦ (p.map f) b)
  have h := congrArg (fun x : ℝ≥0 ↦ (x : ℝ≥0∞)) (conditional_weights_sum p hp f)
  simpa only [ENNReal.coe_finset_sum, ENNReal.coe_one,
    ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] using h

@[simp] lemma marginalSupportPMF_apply {α β : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (b : (p.map f).support) :
    marginalSupportPMF p hp f b = (p.map f) b := rfl

theorem measure_eq_pmfMixture_conditional {β : Type*} [DecidableEq β]
    (p : PMF ℝ) (hp : p.support.Finite) (f : ℝ → β) :
    p.toMeasure =
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    pmfMixture (marginalSupportPMF p hp f)
      (fun b ↦ (Entropy.conditionalPMF p f b).toMeasure)) := by
  exact measure_eq_conditional_mixture p hp f

lemma integral_conditional_variance {β : Type*} [DecidableEq β] [MeasurableSpace β]
    [MeasurableSingletonClass β] (p : PMF ℝ) (hp : p.support.Finite) (f : ℝ → β) :
    (∫ b, ProbabilityTheory.variance (fun u : ℝ ↦ u) (Entropy.conditionalPMF p f b).toMeasure
      ∂(marginalSupportPMF p hp f).toMeasure) = meanConditionalVariance p hp f id := by
  classical
  letI : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  rw [← pmf_sum_eq_integral, meanConditionalVariance_eq]
  apply Finset.sum_congr rfl
  intro b _
  rw [marginalSupportPMF_apply]
  congr 1
  exact (variance_eq_measure_variance (Entropy.conditionalPMF p f b)
    (Entropy.conditionalPMF_support_finite p hp f b) id).symm

end LpSelfSimilar.FiniteProbability
