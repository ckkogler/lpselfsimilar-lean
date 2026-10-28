module

public import LpSelfSimilar.Gaussian.IndependentConditionalGroup
public import LpSelfSimilar.Probability.FinsetConvolution
public import LpSelfSimilar.Analysis.VarianceGrouping

@[expose] public section

/-!
Finite-mixture form of Lemma 3.3. A total expected conditional variance of
`1001*k*r^2` suffices for higher detail at most `100^(-k)`, provided each actual
conditional law lies in an interval of the universal prescribed radius.
Independence, joint reconstruction, greedy grouping, and discarded summands
are all justified within the proof.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace LpSelfSimilar.Gaussian

lemma detail_finset_independent_mixtures_le {I : Type*} (s : Finset I) {Ω : I → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] (p : (i : I) → PMF (Ω i))
    (μ : (i : I) → Ω i → Measure ℝ) [∀ i ω, IsProbabilityMeasure (μ i ω)]
    (c : (i : I) → Ω i → ℝ) {r : ℝ} (hr : 0 < r)
    (hb : ∀ i ω, ∀ᵐ u ∂μ i ω, |u - c i ω| ≤ conditionalRadius * r)
    (hmass : 1000 * r ^ 2 ≤ ∑ i ∈ s, ∫ ω, variance (fun u : ℝ ↦ u) (μ i ω) ∂(p i).toMeasure) :
    detail (finsetConvolution s (fun i ↦ pmfMixture (p i) (μ i))) r ≤ 1 / 100 := by
  classical
  rw [finsetConvolution_eq_finiteConvolution]
  apply detail_independent_mixtures_le_one_hundredth
    (fun j ↦ p ((Fintype.equivFin s).symm j))
    (fun j ↦ μ ((Fintype.equivFin s).symm j))
    (fun j ↦ c ((Fintype.equivFin s).symm j)) hr
  · exact fun j ω ↦ hb _ ω
  · have he : (∑ i ∈ s, ∫ ω, variance (fun u : ℝ ↦ u) (μ i ω) ∂(p i).toMeasure) =
        ∑ j, ∫ ω, variance (fun u : ℝ ↦ u) (μ ((Fintype.equivFin s).symm j) ω)
          ∂(p ((Fintype.equivFin s).symm j)).toMeasure := by
      rw [← Finset.sum_attach]
      exact Fintype.sum_equiv (Fintype.equivFin s)
        (fun i : s ↦ ∫ ω, variance (fun u : ℝ ↦ u) (μ i ω) ∂(p i).toMeasure)
        (fun j ↦ ∫ ω, variance (fun u : ℝ ↦ u) (μ ((Fintype.equivFin s).symm j) ω)
          ∂(p ((Fintype.equivFin s).symm j)).toMeasure)
        (fun i ↦ by
          rw [Equiv.symm_apply_apply])
    exact he ▸ hmass

/-- Lemma 3.3 for arbitrary finite independent mixtures, with explicit absolute
constants. No independence or concentration assumption is added to the input. -/
theorem higherDetail_independent_mixtures {I : Type*} [DecidableEq I] (s : Finset I)
    {Ω : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, MeasurableSingletonClass (Ω i)] (p : (i : I) → PMF (Ω i))
    (μ : (i : I) → Ω i → Measure ℝ) [∀ i ω, IsProbabilityMeasure (μ i ω)]
    (c : (i : I) → Ω i → ℝ) {r : ℝ} (hr : 0 < r)
    (hb : ∀ i ω, ∀ᵐ u ∂μ i ω, |u - c i ω| ≤ conditionalRadius * r)
    (k : ℕ) (hmass : 1001 * (k + 1 : ℕ) * r ^ 2 ≤
      ∑ i ∈ s, ∫ ω, variance (fun u : ℝ ↦ u) (μ i ω) ∂(p i).toMeasure) :
    higherDetail (finsetConvolution s (fun i ↦ pmfMixture (p i) (μ i))) (k + 1) r ≤
      (1 / 100 : ℝ) ^ (k + 1) := by
  let w (i : I) := ∫ ω, variance (fun u : ℝ ↦ u) (μ i ω) ∂(p i).toMeasure
  have hw (i : I) : 0 ≤ w i ∧ w i ≤ r ^ 2 := by
    refine ⟨integral_nonneg (fun ω ↦ variance_nonneg _ _), ?_⟩
    have hrad : (conditionalRadius * r) ^ 2 ≤ r ^ 2 := by
      have : conditionalRadius ^ 2 ≤ 1 := by
        nlinarith [conditionalRadius_pos, conditionalRadius_le_one]
      nlinarith [mul_le_mul_of_nonneg_right this (sq_nonneg r)]
    have hpoint (ω : Ω i) : variance (fun u : ℝ ↦ u) (μ i ω) ≤ r ^ 2 :=
      (variance_le_radius_sq (μ i ω) (hb i ω)).trans hrad
    have h := integral_mono (Integrable.of_finite (μ := (p i).toMeasure))
      (integrable_const (r ^ 2)) hpoint
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using h
  induction k generalizing s with
  | zero =>
    rw [higherDetail_one _ hr]
    have hm : 1000 * r ^ 2 ≤ ∑ i ∈ s, w i := by
      change 1001 * (0 + 1 : ℕ) * r ^ 2 ≤ _ at hmass
      norm_num at hmass
      linarith [sq_nonneg r]
    simpa using detail_finset_independent_mixtures_le s p μ c hr hb hm
  | succ k ih =>
    have htotal : 1000 * r ^ 2 ≤ ∑ i ∈ s, w i := by
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      simp only [Nat.cast_add, Nat.cast_one] at hmass
      nlinarith [mul_nonneg hk (sq_nonneg r)]
    obtain ⟨t, hts, ht, hu⟩ := exists_subset_sum_between s w
      (mul_nonneg (by norm_num) (sq_nonneg r)) (sq_nonneg r)
      (fun i _ ↦ hw i) htotal
    have he : (∑ i ∈ s \ t, w i) + (∑ i ∈ t, w i) = ∑ i ∈ s, w i :=
      Finset.sum_sdiff hts
    have hrest : 1001 * (k + 1 : ℕ) * r ^ 2 ≤ ∑ i ∈ s \ t, w i := by
      simp only [Nat.cast_add, Nat.cast_one] at hmass ⊢
      linarith
    have hg := detail_finset_independent_mixtures_le t p μ c hr hb ht
    have hrec := ih (s \ t) hrest
    rw [finsetConvolution_split s t _ hts]
    have hprod := higherDetail_conv_le
      (finsetConvolution t (fun i ↦ pmfMixture (p i) (μ i)))
      (finsetConvolution (s \ t) (fun i ↦ pmfMixture (p i) (μ i)))
      (by norm_num : 0 < (1 : ℕ)) (Nat.succ_pos k) hr
    rw [higherDetail_one _ hr] at hprod
    have hmul := mul_le_mul hg hrec (higherDetail_nonneg _ _ _) (by norm_num : (0 : ℝ) ≤ 1 / 100)
    have horder : 1 + (k + 1) = k + 1 + 1 := by omega
    rw [horder] at hprod
    exact hprod.trans (hmul.trans_eq (by ring))

end LpSelfSimilar.Gaussian
