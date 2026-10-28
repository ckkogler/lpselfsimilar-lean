module

public import LpSelfSimilar.Entropy.CellEntropyVariance
public import LpSelfSimilar.Entropy.ConditionalStatistic
public import LpSelfSimilar.Entropy.GridVariance
public import LpSelfSimilar.Probability.FiniteJensen

@[expose] public section

/-!
The entropy-to-variance inequality of Lemma 3.5 for finite real laws. First
condition on a coarse grid cell, average the fine-grid entropy, and use finite
Jensen. Then average over the coarse shift and apply integral Jensen twice.
-/

open MeasureTheory Set Real
open scoped ENNReal

namespace LpSelfSimilar.Entropy

lemma gridEntropy_sub_gridEntropyAt_le_conditional (p : PMF ℝ) (hp : p.support.Finite)
    (s t u : ℝ) :
    gridEntropy p hp u - gridEntropyAt p hp s t ≤
    (letI : Fintype (p.map (quantize s t)).support :=
      (show (p.map (quantize s t)).support.Finite from by
        simpa using hp.image (quantize s t)).fintype
    ∑ b : (p.map (quantize s t)).support, ((p.map (quantize s t)) b).toReal *
      gridEntropy (conditionalPMF p (quantize s t) b)
        (conditionalPMF_support_finite p hp (quantize s t) b) u) := by
  classical
  let f := quantize s t
  let hpf : (p.map f).support.Finite := by simpa using hp.image f
  letI : Fintype (p.map f).support := hpf.fintype
  let q (b : (p.map f).support) := conditionalPMF p f b
  let hq (b : (p.map f).support) := conditionalPMF_support_finite p hp f b
  let m (b : (p.map f).support) := ((p.map f) b).toReal
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  have hi : Integrable (fun v ↦ ∑ b, m b * gridEntropyAt (q b) (hq b) u v) μ := by
    apply integrable_finsetSum
    intro b _
    exact (integrable_gridEntropyAt (q b) (hq b) u).const_mul _
  have he (v : ℝ) : gridEntropyAt p hp u v - gridEntropyAt p hp s t ≤
      ∑ b, m b * gridEntropyAt (q b) (hq b) u v :=
    entropy_sub_le_conditional_statistic p hp f (quantize u v)
  have hh := integral_mono ((integrable_gridEntropyAt p hp u).sub (integrable_const _)) hi he
  simp only [Pi.sub_apply] at hh
  rw [integral_sub (integrable_gridEntropyAt p hp u) (integrable_const _),
    integral_finsetSum Finset.univ (fun b _ ↦
      (integrable_gridEntropyAt (q b) (hq b) u).const_mul (m b))] at hh
  simp_rw [integral_const_mul] at hh
  simpa [gridEntropy, μ, q, hq, m, f] using hh

lemma gridEntropy_sub_gridEntropyAt_le_ten_fourthRoot (p : PMF ℝ) (hp : p.support.Finite)
    {s : ℝ} (hs : 0 < s) (t : ℝ) :
    gridEntropy p hp (s / 4) - gridEntropyAt p hp s t ≤
      10 * Real.sqrt (Real.sqrt (gridVarianceAt p hp s t)) := by
  classical
  let f := quantize s t
  let hpf : (p.map f).support.Finite := by simpa using hp.image f
  letI : Fintype (p.map f).support := hpf.fintype
  let q (b : (p.map f).support) := conditionalPMF p f b
  let hq (b : (p.map f).support) := conditionalPMF_support_finite p hp f b
  let m (b : (p.map f).support) := ((p.map f) b).toReal
  let v (b : (p.map f).support) := FiniteProbability.variance (q b) (hq b) id / s ^ 2
  have hm : ∑ b, m b = 1 := by
    dsimp only [m]
    rw [← Finset.sum_subtype hpf.toFinset (by simp : ∀ b, b ∈ hpf.toFinset ↔ b ∈ (p.map f).support) (fun b : ℤ ↦ ((p.map f) b).toReal)]
    exact sum_support_toReal _ _
  have hv (b : (p.map f).support) : 0 ≤ v b := by
    exact div_nonneg (FiniteProbability.variance_nonneg _ _ _) (sq_nonneg _)
  have hc (b : (p.map f).support) : gridEntropy (q b) (hq b) (s / 4) ≤
      10 * Real.sqrt (Real.sqrt (v b)) :=
    fine_gridEntropy_le_ten_fourthRoot_variance (q b) (hq b)
      (conditional_grid_support p hs t b) hs (by ring_nf; exact le_rfl)
  have he : (∑ b, m b * v b) = gridVarianceAt p hp s t := by
    unfold gridVarianceAt
    rw [FiniteProbability.meanConditionalVariance_eq]
    simp only [v, m, q, hq, f, mul_div_assoc, Finset.sum_div]
  calc
    gridEntropy p hp (s / 4) - gridEntropyAt p hp s t ≤
      ∑ b, m b * gridEntropy (q b) (hq b) (s / 4) :=
        gridEntropy_sub_gridEntropyAt_le_conditional p hp s t (s / 4)
    _ ≤ ∑ b, m b * (10 * Real.sqrt (Real.sqrt (v b))) :=
      Finset.sum_le_sum (fun b _ ↦ mul_le_mul_of_nonneg_left (hc b) ENNReal.toReal_nonneg)
    _ = 10 * ∑ b, m b * Real.sqrt (Real.sqrt (v b)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
    _ ≤ 10 * Real.sqrt (Real.sqrt (∑ b, m b * v b)) :=
      mul_le_mul_of_nonneg_left
        (weighted_fourthRoot_le_fourthRoot_weighted m v
          (fun _ ↦ ENNReal.toReal_nonneg) hm hv) (by norm_num)
    _ = _ := by rw [he]

/-- Lemma 3.5: the entropy increment at a factor-four refinement is bounded by
    ten times the fourth root of normalized mean conditional variance. -/
theorem gridEntropy_increment_le_ten_fourthRoot_scaleVariance
    (p : PMF ℝ) (hp : p.support.Finite) {s : ℝ} (hs : 0 < s) :
    gridEntropy p hp (s / 4) - gridEntropy p hp s ≤
      10 * Real.sqrt (Real.sqrt (scaleVariance p hp s)) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hi := integrable_gridVarianceAt p hp hs
  have hn := ae_of_all μ (gridVarianceAt_nonneg p hp s)
  have hroot := integrable_sqrt_of_nonneg hi hn
  have hroot2 := integrable_sqrt_of_nonneg hroot (ae_of_all _ (fun _ ↦ Real.sqrt_nonneg _))
  have h := integral_mono ((integrable_const _).sub (integrable_gridEntropyAt p hp s))
    (hroot2.const_mul 10) (gridEntropy_sub_gridEntropyAt_le_ten_fourthRoot p hp hs)
  have hleft : (∫ t, gridEntropy p hp (s / 4) - gridEntropyAt p hp s t ∂μ) =
      gridEntropy p hp (s / 4) - gridEntropy p hp s := by
    rw [integral_sub (integrable_const _) (integrable_gridEntropyAt p hp s)]
    simp [gridEntropy, μ]
  simp only [Pi.sub_apply] at h
  rw [hleft, integral_const_mul] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (integral_sqrt_le_sqrt_integral hroot
    (ae_of_all _ (fun _ ↦ Real.sqrt_nonneg _))).trans
      (Real.sqrt_le_sqrt (integral_sqrt_le_sqrt_integral hi hn))

end LpSelfSimilar.Entropy
