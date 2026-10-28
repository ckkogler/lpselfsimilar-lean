module

public import LpSelfSimilar.Entropy.Conditioning
public import LpSelfSimilar.Probability.ParameterizedConditionalLaw

@[expose] public section

/-!
Discrete conditional probability formulas for actual regular conditional laws.

At a positive-mass statistic value, the conditional law is the normalized
restriction of the original PMF. This identifies the jointly measurable
parameterized conditional kernel with the explicit finite grid-cell formulas.
Null statistic values are excluded only from this pointwise formula; the
conditional kernel itself is defined everywhere and remains a Markov kernel.
-/

open MeasureTheory ProbabilityTheory Set

namespace LpSelfSimilar

lemma conditionalPMF_toMeasure (p : PMF ℝ) (f : ℝ → ℤ) (hf : Measurable f)
    (b : (p.map f).support) :
    (Entropy.conditionalPMF p f b).toMeasure =
      ((p.map f) b)⁻¹ • p.toMeasure.restrict {x | f x = b} := by
  classical
  have hb : MeasurableSet {x | f x = b} := hf (measurableSet_singleton b.val)
  ext s hs
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs,
    PMF.toMeasure_apply _ hs, PMF.toMeasure_apply _ (hs.inter hb),
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ s <;> by_cases hfx : f x = b
  all_goals simp [Set.indicator, Entropy.conditionalPMF_apply, hx, hfx,
    div_eq_mul_inv, mul_comm]

lemma fst_jointStatisticLaw (p : PMF ℝ) (f : ℝ → ℤ) (hf : Measurable f) :
    (p.toMeasure.map (fun x ↦ (f x, x))).fst = (p.map f).toMeasure := by
  have hpair : Measurable (fun x : ℝ ↦ (f x, x)) := hf.prodMk measurable_id
  rw [Measure.fst, Measure.map_map measurable_fst hpair]
  exact PMF.toMeasure_map f p hf

/-- Conditioning a discrete law on an atom agrees with normalized restriction. -/
theorem condKernel_jointStatistic_eq_conditionalPMF (p : PMF ℝ) (f : ℝ → ℤ)
    (hf : Measurable f) (b : (p.map f).support) :
    (p.toMeasure.map (fun x ↦ (f x, x))).condKernel b =
      (Entropy.conditionalPMF p f b).toMeasure := by
  have hpair : Measurable (fun x : ℝ ↦ (f x, x)) := hf.prodMk measurable_id
  have hm : (p.toMeasure.map (fun x ↦ (f x, x))).fst {b.val} = (p.map f) b := by
    rw [fst_jointStatisticLaw p f hf, PMF.toMeasure_apply_singleton _ _
      (measurableSet_singleton _)]
  have hn : (p.toMeasure.map (fun x ↦ (f x, x))).fst {b.val} ≠ 0 := by
    rw [hm]
    exact b.property
  rw [conditionalPMF_toMeasure p f hf b]
  ext s hs
  rw [Measure.condKernel_apply_of_ne_zero hn, hm,
    Measure.map_apply hpair ((measurableSet_singleton b.val).prod hs),
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs]
  congr 2
  ext x
  simp only [mem_preimage, mem_prod, mem_singleton_iff, mem_inter_iff, mem_ofPred_eq]
  exact and_comm

/-- The parameterized law has the explicit PMF formula at each nonnull cell. -/
theorem parameterizedConditionalLaw_eq_conditionalPMF {T : Type*} [MeasurableSpace T]
    (p : PMF ℝ) (f : T × ℝ → ℤ) (hf : Measurable f) (t : T)
    (b : (p.map (fun x ↦ f (t, x))).support) :
    parameterizedConditionalLaw p.toMeasure f hf (t, b.val) =
      (Entropy.conditionalPMF p (fun x ↦ f (t, x)) b).toMeasure := by
  have ht : Measurable (fun x : ℝ ↦ f (t, x)) := hf.comp measurable_prodMk_left
  have h := (parameterizedJointLaw p.toMeasure f hf).condKernel_apply_eq_condKernel t
  have hm : (parameterizedJointLaw p.toMeasure f hf).fst t =
      (p.map (fun x ↦ f (t, x))).toMeasure := by
    rw [Kernel.fst_apply, parameterizedJointLaw_apply]
    exact fst_jointStatisticLaw p _ ht
  rw [hm] at h
  have he := (ae_iff_of_countable.mp h) b.val (by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    exact b.property)
  apply he.trans
  simpa only [parameterizedJointLaw_apply] using
    condKernel_jointStatistic_eq_conditionalPMF p _ ht b

end LpSelfSimilar
