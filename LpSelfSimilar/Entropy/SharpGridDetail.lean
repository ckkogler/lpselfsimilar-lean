module

public import LpSelfSimilar.Entropy.GridDetail
public import LpSelfSimilar.Gaussian.SharpFiniteConditioning

@[expose] public section

/-!
From the shift-averaged grid variances of finite laws to their higher Gaussian
detail. A deterministic shift at least as good as its average replaces random
shifts. Actual cell-conditioned laws reconstruct each summand exactly.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set

namespace LpSelfSimilar.Entropy

/-- Deterministic grid-conditioning form of Lemma 3.3. -/
theorem higherDetail_le_of_gridVarianceAt_explicit {I : Type*} [DecidableEq I] (S : Finset I)
    (p : I → PMF ℝ) (hp : ∀ i, (p i).support.Finite) (s t : I → ℝ)
    {r : ℝ} (hr : 0 < r) (hs : ∀ i, 0 < s i)
    (hsmall : ∀ i, s i ≤ (1 / 10000 : ℝ) * r) (k : ℕ)
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
  refine Gaussian.higherDetail_independent_mixtures_explicit S q μ c hr ?_ k ?_
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
are proved. The revised radius is exactly 10^-4. -/
theorem higherDetail_le_of_scaleVariance_explicit {I : Type*} [DecidableEq I] (S : Finset I)
    (p : I → PMF ℝ) (hp : ∀ i, (p i).support.Finite) (s : I → ℝ)
    {r : ℝ} (hr : 0 < r) (hs : ∀ i, 0 < s i)
    (hsmall : ∀ i, s i ≤ (1 / 10000 : ℝ) * r) (k : ℕ)
    (hbudget : 1001 * (k + 1 : ℕ) * r ^ 2 ≤ ∑ i ∈ S, s i ^ 2 * scaleVariance (p i) (hp i) (s i)) :
    Gaussian.higherDetail (finsetConvolution S (fun i ↦ (p i).toMeasure)) (k + 1) r ≤
      (1 / 100 : ℝ) ^ (k + 1) := by
  choose t ht using fun i ↦ exists_shift_gridVarianceAt_ge (p i) (hp i) (hs i)
  apply higherDetail_le_of_gridVarianceAt_explicit S p hp s t hr hs hsmall k
  apply hbudget.trans
  exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_left (ht i) (sq_nonneg _))

end LpSelfSimilar.Entropy
