module

public import LpSelfSimilar.Entropy.Grid
public import LpSelfSimilar.Probability.ConditionalMoments

@[expose] public section

/-!
The normalized mean conditional variance at a shifted grid, and its average
over a uniform shift. The finite formulas represent genuine conditional laws;
measurability and boundedness are proved rather than assumed.
-/

open MeasureTheory Set Real

namespace LpSelfSimilar.Entropy

lemma conditional_grid_support (p : PMF ℝ) {s : ℝ} (hs : 0 < s) (t : ℝ)
    (b : (p.map (quantize s t)).support) :
    (conditionalPMF p (quantize s t) b).support ⊆
      Icc (((b : ℤ) - t) * s) (((b : ℤ) + 1 - t) * s) := by
  intro x hx
  rw [conditionalPMF_support] at hx
  have hlo := Int.floor_le (x / s + t)
  have hhi := Int.lt_floor_add_one (x / s + t)
  change ⌊x / s + t⌋ = b ∧ x ∈ p.support at hx
  rw [hx.1] at hlo hhi
  constructor
  · exact (le_div_iff₀ hs).mp (by linarith)
  · exact (div_le_iff₀ hs).mp (by linarith)

lemma grid_fiberVariance_le (p : PMF ℝ) (hp : p.support.Finite)
    {s : ℝ} (hs : 0 < s) (t x : ℝ) (hx : x ∈ p.support) :
    FiniteProbability.fiberVariance p hp (quantize s t) id (quantize s t x) ≤ s ^ 2 := by
  let b : (p.map (quantize s t)).support := ⟨quantize s t x, by
    rw [PMF.support_map]; exact ⟨x, hx, rfl⟩⟩
  rw [FiniteProbability.fiberVariance_eq_conditional p hp (quantize s t) id b]
  apply FiniteProbability.variance_le_sq_of_diameter _ _ id hs.le
  intro a ha c hc
  rw [conditionalPMF_support] at ha hc
  exact (abs_sub_lt_of_quantize_eq hs (ha.1.trans hc.1.symm)).le

/-- `s⁻²` times the variance remaining after observing the shifted grid cell. -/
noncomputable def gridVarianceAt (p : PMF ℝ) (hp : p.support.Finite) (s t : ℝ) : ℝ :=
  FiniteProbability.meanConditionalVariance p hp (quantize s t) id / s ^ 2

/-- Scale-averaged normalized conditional variance `V(X;s)` from Section 3. -/
noncomputable def scaleVariance (p : PMF ℝ) (hp : p.support.Finite) (s : ℝ) : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, gridVarianceAt p hp s t

lemma gridVarianceAt_nonneg (p : PMF ℝ) (hp : p.support.Finite) (s t : ℝ) :
    0 ≤ gridVarianceAt p hp s t :=
  div_nonneg (FiniteProbability.meanConditionalVariance_nonneg _ _ _ _) (sq_nonneg _)

lemma gridVarianceAt_le_one (p : PMF ℝ) (hp : p.support.Finite)
    {s : ℝ} (hs : 0 < s) (t : ℝ) : gridVarianceAt p hp s t ≤ 1 := by
  apply (div_le_one (sq_pos_of_pos hs)).mpr
  change FiniteProbability.expectation p hp _ ≤ s ^ 2
  rw [← FiniteProbability.expectation_const p hp (s ^ 2)]
  exact FiniteProbability.expectation_mono p hp (grid_fiberVariance_le p hp hs t)

lemma measurable_gridVarianceAt (p : PMF ℝ) (hp : p.support.Finite) :
    Measurable (fun q : ℝ × ℝ ↦ gridVarianceAt p hp q.1 q.2) := by
  unfold gridVarianceAt FiniteProbability.meanConditionalVariance
    FiniteProbability.fiberVariance FiniteProbability.expectation
  simp_rw [marginal_toReal_eq_finite_sum p hp]
  apply Measurable.div _ (by fun_prop)
  apply Finset.measurable_sum
  intro a _
  apply Measurable.const_mul
  apply Measurable.sub
  · apply Measurable.div
    · apply Finset.measurable_sum
      intro b _
      apply Measurable.const_mul
      apply Measurable.ite
      · apply measurableSet_eq_fun <;> unfold quantize <;> fun_prop
      · exact measurable_const
      · exact measurable_const
    · apply Finset.measurable_sum
      intro b _
      apply Measurable.ite
      · apply measurableSet_eq_fun <;> unfold quantize <;> fun_prop
      · exact measurable_const
      · exact measurable_const
  · apply Measurable.pow_const
    apply Measurable.div
    · apply Finset.measurable_sum
      intro b _
      apply Measurable.const_mul
      apply Measurable.ite
      · apply measurableSet_eq_fun <;> unfold quantize <;> fun_prop
      · exact measurable_const
      · exact measurable_const
    · apply Finset.measurable_sum
      intro b _
      apply Measurable.ite
      · apply measurableSet_eq_fun <;> unfold quantize <;> fun_prop
      · exact measurable_const
      · exact measurable_const

lemma integrable_gridVarianceAt (p : PMF ℝ) (hp : p.support.Finite)
    {s : ℝ} (hs : 0 < s) : IntegrableOn (gridVarianceAt p hp s) (Icc (0 : ℝ) 1) volume := by
  have hm := (measurable_gridVarianceAt p hp).comp (f := fun t : ℝ ↦ (s, t))
    (measurable_const.prodMk measurable_id)
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro t
  change ‖gridVarianceAt p hp s t‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (gridVarianceAt_nonneg p hp s t)]
  exact gridVarianceAt_le_one p hp hs t

lemma scaleVariance_nonneg (p : PMF ℝ) (hp : p.support.Finite) (s : ℝ) :
    0 ≤ scaleVariance p hp s := integral_nonneg (gridVarianceAt_nonneg p hp s)

lemma scaleVariance_le_one (p : PMF ℝ) (hp : p.support.Finite)
    {s : ℝ} (hs : 0 < s) : scaleVariance p hp s ≤ 1 := by
  have h := integral_mono (integrable_gridVarianceAt p hp hs) (integrable_const (1 : ℝ))
    (gridVarianceAt_le_one p hp hs)
  simpa [scaleVariance] using h

end LpSelfSimilar.Entropy
