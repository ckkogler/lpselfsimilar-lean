module

public import LpSelfSimilar.Entropy.GridVariance
public import LpSelfSimilar.Probability.ConditionalLaw
public import LpSelfSimilar.Gaussian.ConditionalVariance
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section

/-!
From the shift-averaged grid variances of finite laws to their higher Gaussian
detail. A deterministic shift at least as good as its average replaces random
shifts. Actual cell-conditioned laws reconstruct each summand exactly.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace LpSelfSimilar.Entropy

lemma exists_shift_gridVarianceAt_ge (p : PMF ℝ) (hp : p.support.Finite)
    {s : ℝ} (hs : 0 < s) : ∃ t : ℝ, scaleVariance p hp s ≤ gridVarianceAt p hp s t := by
  letI : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := ⟨by simp⟩
  exact exists_integral_le (integrable_gridVarianceAt p hp hs)

lemma conditional_grid_radius (p : PMF ℝ) {s : ℝ} (hs : 0 < s) (t : ℝ)
    (b : (p.map (quantize s t)).support) :
    ∀ᵐ u ∂(conditionalPMF p (quantize s t) b).toMeasure,
      |u - (((b : ℤ) : ℝ) - t) * s| ≤ s := by
  rw [← PMF.restrict_toMeasure_support]
  filter_upwards [ae_restrict_mem (PMF.support_countable _).measurableSet] with u hu
  have h := conditional_grid_support p hs t b hu
  apply abs_le.mpr
  constructor <;> nlinarith [h.1, h.2]

/-- Deterministic grid-conditioning form of Lemma 3.3. -/
theorem higherDetail_le_of_gridVarianceAt {I : Type*} [DecidableEq I] (S : Finset I)
    (p : I → PMF ℝ) (hp : ∀ i, (p i).support.Finite) (s t : I → ℝ)
    {r : ℝ} (hr : 0 < r) (hs : ∀ i, 0 < s i)
    (hsmall : ∀ i, s i ≤ Gaussian.conditionalRadius * r) (k : ℕ)
    (hbudget : 1001 * (k + 1 : ℕ) * r ^ 2 ≤ ∑ i ∈ S, s i ^ 2 * gridVarianceAt (p i) (hp i) (s i) (t i)) :
    Gaussian.higherDetail (finsetConvolution S (fun i ↦ (p i).toMeasure)) (k + 1) r ≤
      (1 / 100 : ℝ) ^ (k + 1) := by
  classical
  let f (i : I) := quantize (s i) (t i)
  let Ω (i : I) := ((p i).map (f i)).support
  letI (i : I) : Fintype (Ω i) :=
    (show ((p i).map (f i)).support.Finite from by simpa using (hp i).image (f i)).fintype
  let q (i : I) := FiniteProbability.marginalSupportPMF (p i) (hp i) (f i)
  let μ (i : I) (b : Ω i) := (conditionalPMF (p i) (f i) b).toMeasure
  let c (i : I) (b : Ω i) := (((b : ℤ) : ℝ) - t i) * s i
  have he (i : I) : (p i).toMeasure = pmfMixture (q i) (μ i) :=
    FiniteProbability.measure_eq_pmfMixture_conditional (p i) (hp i) (f i)
  simp_rw [he]
  refine Gaussian.higherDetail_independent_mixtures S q μ c hr ?_ k ?_
  · intro i b
    exact (conditional_grid_radius (p i) (hs i) (t i) b).mono (fun _ h ↦ h.trans (hsmall i))
  · have heq : (∑ i ∈ S, ∫ b, variance (fun u : ℝ ↦ u) (μ i b) ∂(q i).toMeasure) =
        ∑ i ∈ S, s i ^ 2 * gridVarianceAt (p i) (hp i) (s i) (t i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [FiniteProbability.integral_conditional_variance]
      unfold gridVarianceAt
      dsimp only [f]
      field_simp [(hs i).ne']
    exact heq ▸ hbudget

/-- Averaged grid variances suffice: all conditioning and independence steps
are proved. This is the form used for rational Bernoulli digit blocks. -/
theorem higherDetail_le_of_scaleVariance {I : Type*} [DecidableEq I] (S : Finset I)
    (p : I → PMF ℝ) (hp : ∀ i, (p i).support.Finite) (s : I → ℝ)
    {r : ℝ} (hr : 0 < r) (hs : ∀ i, 0 < s i)
    (hsmall : ∀ i, s i ≤ Gaussian.conditionalRadius * r) (k : ℕ)
    (hbudget : 1001 * (k + 1 : ℕ) * r ^ 2 ≤ ∑ i ∈ S, s i ^ 2 * scaleVariance (p i) (hp i) (s i)) :
    Gaussian.higherDetail (finsetConvolution S (fun i ↦ (p i).toMeasure)) (k + 1) r ≤
      (1 / 100 : ℝ) ^ (k + 1) := by
  choose t ht using fun i ↦ exists_shift_gridVarianceAt_ge (p i) (hp i) (hs i)
  apply higherDetail_le_of_gridVarianceAt S p hp s t hr hs hsmall k
  apply hbudget.trans
  exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (ht i) (sq_nonneg _))

end LpSelfSimilar.Entropy
