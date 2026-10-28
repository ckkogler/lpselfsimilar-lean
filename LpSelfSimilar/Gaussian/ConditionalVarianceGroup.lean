module

public import LpSelfSimilar.Gaussian.MixtureDetail
public import LpSelfSimilar.Gaussian.ShortIntervals
public import LpSelfSimilar.Probability.PMFMixture
public import LpSelfSimilar.Probability.VarianceConcentration

@[expose] public section

/-!
The one-group conditional-variance estimate in Lemma 3.3, for finite conditioning
spaces. Each conditional law is an actual probability measure in a short
interval. Independence of the conditional variances gives Chebyshev's bound;
convexity and the small-summand lemma then control the unconditional mixture.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Set

namespace LpSelfSimilar.Gaussian

theorem conditional_group_detail_le {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (p : PMF Ω) {n : ℕ}
    (μ : Ω → Fin n → Measure ℝ) [∀ ω i, IsProbabilityMeasure (μ ω i)]
    (c : Ω → Fin n → ℝ) {ε r A : ℝ} (hε : 0 ≤ ε) (hr : 0 < r) (hA : 0 < A)
    (hb : ∀ ω i, ∀ᵐ u ∂μ ω i, |u - c ω i| ≤ ε * r)
    (hind : iIndepFun (fun i ω ↦ variance (fun u : ℝ ↦ u) (μ ω i)) p.toMeasure)
    (hmass : A * r ^ 2 ≤ ∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (μ ω i) ∂p.toMeasure) :
    detail (pmfMixture p (fun ω ↦ finiteConvolution (μ ω))) r ≤
      2 / A + generalSmallSummandConstant * ε + 4 * ε ^ 2 / A := by
  let W (i : Fin n) (ω : Ω) := variance (fun u : ℝ ↦ u) (μ ω i)
  let m := ∑ i, ∫ ω, W i ω ∂p.toMeasure
  let V (ω : Ω) := ∑ i, W i ω
  have hm : 0 < m := (mul_pos hA (sq_pos_of_pos hr)).trans_le hmass
  have hW (i : Fin n) : ∀ᵐ ω ∂p.toMeasure, W i ω ∈ Icc 0 ((ε * r) ^ 2) :=
    ae_of_all _ (fun ω ↦ ⟨variance_nonneg _ _, variance_le_radius_sq (μ ω i) (hb ω i)⟩)
  have hprob := probability_sum_lt_half_mean_le p.toMeasure W
    (fun _ ↦ measurable_of_countable _) hind (sq_nonneg (ε * r)) hW hm
  let E := {ω | V ω < m / 2}
  have hE : MeasurableSet E := Set.toFinite E |>.measurableSet
  have hpoint (ω : Ω) : detail (finiteConvolution (μ ω)) r ≤
      (2 * r ^ 2 / m + generalSmallSummandConstant * ε) + E.indicator (fun _ ↦ 1) ω := by
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      have hn : 0 ≤ 2 * r ^ 2 / m + generalSmallSummandConstant * ε := by
        positivity [generalSmallSummandConstant_pos]
      exact (detail_le_one _ hr).trans (by linarith)
    · rw [Set.indicator_of_notMem he]
      have hV : m / 2 ≤ V ω := le_of_not_gt he
      have hs := small_summands_intervals (μ ω) (c ω) hε hr (hb ω)
      have hv : 0 ≤ V ω := Finset.sum_nonneg (fun i _ ↦ variance_nonneg _ _)
      have hf : r ^ 2 / (r ^ 2 + V ω) ≤ 2 * r ^ 2 / m := by
        apply (div_le_div_iff₀ (by positivity : 0 < r ^ 2 + V ω) hm).2
        nlinarith [mul_le_mul_of_nonneg_left hV (sq_nonneg r)]
      change detail (finiteConvolution (μ ω)) r ≤ r ^ 2 / (r ^ 2 + V ω) + _ at hs
      linarith
  have hconv := detail_finiteMixture_le (fun ω ↦ (p ω).toNNReal)
    (fun ω ↦ finiteConvolution (μ ω)) hr
  change detail (pmfMixture p (fun ω ↦ finiteConvolution (μ ω))) r ≤
    ∑ ω, (p ω).toReal * detail (finiteConvolution (μ ω)) r at hconv
  rw [pmf_sum_eq_integral] at hconv
  have hi := integral_mono (Integrable.of_finite (μ := p.toMeasure))
    (Integrable.of_finite (μ := p.toMeasure)) hpoint
  have he : (∫ ω, (2 * r ^ 2 / m + generalSmallSummandConstant * ε) +
      E.indicator (fun _ ↦ 1) ω ∂p.toMeasure) =
      2 * r ^ 2 / m + generalSmallSummandConstant * ε + p.toMeasure.real E := by
    rw [integral_add (integrable_const _) (Integrable.of_finite), integral_const]
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    congr 1
    exact integral_indicator_one (μ := p.toMeasure) hE
  rw [he] at hi
  have h1 : 2 * r ^ 2 / m ≤ 2 / A := by
    apply (div_le_div_iff₀ hm hA).2
    nlinarith [hmass]
  have h2 : 4 * (ε * r) ^ 2 / m ≤ 4 * ε ^ 2 / A := by
    apply (div_le_div_iff₀ hm hA).2
    nlinarith [mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 4 * ε ^ 2)]
  exact hconv.trans (hi.trans (by
    change _ ≤ _
    change p.toMeasure.real E ≤ 4 * (ε * r) ^ 2 / m at hprob
    linarith))

/-- One absolute choice of the conditional interval radius. -/
noncomputable def conditionalRadius : ℝ := 1 / (1000 * (generalSmallSummandConstant + 1))

lemma conditionalRadius_pos : 0 < conditionalRadius := by
  unfold conditionalRadius
  positivity [generalSmallSummandConstant_pos]

lemma conditionalRadius_le_one : conditionalRadius ≤ 1 := by
  unfold conditionalRadius
  apply (div_le_iff₀ (by positivity [generalSmallSummandConstant_pos])).2
  linarith [generalSmallSummandConstant_pos]

lemma replacement_at_conditionalRadius_le :
    generalSmallSummandConstant * conditionalRadius ≤ 1 / 1000 := by
  unfold conditionalRadius
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity [generalSmallSummandConstant_pos])).2
  linarith

/-- The quantitative one-group conclusion in Lemma 3.3. -/
theorem conditional_group_detail_le_one_hundredth {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (p : PMF Ω) {n : ℕ}
    (μ : Ω → Fin n → Measure ℝ) [∀ ω i, IsProbabilityMeasure (μ ω i)]
    (c : Ω → Fin n → ℝ) {r : ℝ} (hr : 0 < r)
    (hb : ∀ ω i, ∀ᵐ u ∂μ ω i, |u - c ω i| ≤ conditionalRadius * r)
    (hind : iIndepFun (fun i ω ↦ variance (fun u : ℝ ↦ u) (μ ω i)) p.toMeasure)
    (hmass : 1000 * r ^ 2 ≤ ∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (μ ω i) ∂p.toMeasure) :
    detail (pmfMixture p (fun ω ↦ finiteConvolution (μ ω))) r ≤ 1 / 100 := by
  have h := conditional_group_detail_le p μ c conditionalRadius_pos.le hr
    (by norm_num : (0 : ℝ) < 1000) hb hind hmass
  have hs : conditionalRadius ^ 2 ≤ 1 := by
    nlinarith [conditionalRadius_pos, conditionalRadius_le_one]
  nlinarith [replacement_at_conditionalRadius_le]

/-- The product step of Lemma 3.3 for finitely conditioned independent groups.
The construction of the groups from a total variance budget is separate. -/
theorem higherDetail_conditioned_groups {k : ℕ} {Ω : Fin (k + 1) → Type*}
    [∀ j, Fintype (Ω j)] [∀ j, MeasurableSpace (Ω j)] [∀ j, MeasurableSingletonClass (Ω j)]
    (p : (j : Fin (k + 1)) → PMF (Ω j)) (n : Fin (k + 1) → ℕ)
    (μ : (j : Fin (k + 1)) → Ω j → Fin (n j) → Measure ℝ)
    [∀ j ω i, IsProbabilityMeasure (μ j ω i)]
    (c : (j : Fin (k + 1)) → Ω j → Fin (n j) → ℝ) {r : ℝ} (hr : 0 < r)
    (hb : ∀ j ω i, ∀ᵐ u ∂μ j ω i, |u - c j ω i| ≤ conditionalRadius * r)
    (hind : ∀ j, iIndepFun (fun i ω ↦ variance (fun u : ℝ ↦ u) (μ j ω i)) (p j).toMeasure)
    (hmass : ∀ j, 1000 * r ^ 2 ≤ ∑ i, ∫ ω, variance (fun u : ℝ ↦ u) (μ j ω i) ∂(p j).toMeasure) :
    higherDetail (finiteConvolution (fun j ↦ pmfMixture (p j)
      (fun ω ↦ finiteConvolution (μ j ω)))) (k + 1) r ≤ (1 / 100 : ℝ) ^ (k + 1) := by
  apply (higherDetail_finiteConvolution_le _ hr).trans
  calc
    _ ≤ ∏ _j : Fin (k + 1), (1 / 100 : ℝ) := by
      apply Finset.prod_le_prod
      · intro j _
        exact detail_nonneg _ _
      · intro j _
        exact conditional_group_detail_le_one_hundredth (p j) (μ j) (c j) hr (hb j) (hind j) (hmass j)
    _ = _ := by simp

end LpSelfSimilar.Gaussian
