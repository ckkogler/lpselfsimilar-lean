module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Bernoulli.ScaledDigits
public import LpSelfSimilar.Bernoulli.PrefixTail
public import LpSelfSimilar.Gaussian.SmallSummands
public import LpSelfSimilar.Gaussian.FiniteApproximation

@[expose] public section

/-!
The small-summand estimate for an entire scaled Bernoulli convolution. Finite
prefixes have independent fair-sign laws with exact variances. Their geometric
variance sums converge; dominated convergence and Fatou pass the estimate to
the infinite series, without an absolute-continuity assumption.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Filter
open scoped Topology NNReal

namespace LpSelfSimilar.Bernoulli

lemma tendsto_prefix_variance {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l < 1) (a : ℝ) :
    Tendsto (fun n ↦ ∑ j : Fin n, (a * l ^ (j : ℕ)) ^ 2) atTop
      (𝓝 (a ^ 2 / (1 - l ^ 2))) := by
  have hlsq : l ^ 2 < 1 := by nlinarith
  have h := ((hasSum_geometric_of_lt_one (sq_nonneg l) hlsq).mul_left (a ^ 2)).tendsto_sum_nat
  have he (n : ℕ) : (∑ j : Fin n, (a * l ^ (j : ℕ)) ^ 2) =
      ∑ j ∈ Finset.range n, a ^ 2 * (l ^ 2) ^ j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j ↦ a ^ 2 * (l ^ 2) ^ j) n]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (j : ℕ) 2]
  simp_rw [he]
  simpa only [div_eq_mul_inv] using h

/-- An infinite tail obeys the same finite small-summand bound. -/
theorem detail_scaled_convolution_le {l a ε r : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l < 1) (ha : 0 ≤ a)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hr : 0 < r) (haε : a ≤ ε * r) :
    Gaussian.detail ((convolution l).map (fun x ↦ a * x)) r ≤
      r ^ 2 / (r ^ 2 + a ^ 2 / (1 - l ^ 2)) + Gaussian.smallSummandConstant * ε := by
  have hlabs : |l| < 1 := by simpa only [abs_of_nonneg hl0] using hl1
  have hlsq : l ^ 2 < 1 := by nlinarith
  have hvar : 0 ≤ a ^ 2 / (1 - l ^ 2) := by positivity
  have hd : r ^ 2 + a ^ 2 / (1 - l ^ 2) ≠ 0 := by positivity
  have hC : Tendsto (fun n ↦ r ^ 2 / (r ^ 2 + ∑ j : Fin n, (a * l ^ (j : ℕ)) ^ 2) +
      Gaussian.smallSummandConstant * ε) atTop
      (𝓝 (r ^ 2 / (r ^ 2 + a ^ 2 / (1 - l ^ 2)) + Gaussian.smallSummandConstant * ε)) :=
    (tendsto_const_nhds.div (tendsto_const_nhds.add
    (tendsto_prefix_variance hl0 hl1 a)) hd).add_const (Gaussian.smallSummandConstant * ε)
  have hme : (convolution l).map (fun x ↦ a * x) = digitSpace.map (fun w ↦ a * series l w) := by
    rw [convolution, Measure.map_map (by fun_prop) (measurable_series l)]
    rfl
  rw [hme]
  apply Gaussian.detail_map_le_of_tendsto digitSpace
    (fun n ↦ by fun_prop) (by fun_prop)
    (ae_of_all _ (fun w ↦ tendsto_const_nhds.mul (tendsto_digitSum hlabs w))) hr
    (by positivity [Gaussian.smallSummandConstant_nonneg]) hC
  intro n
  rw [scaled_prefix_law]
  let v (j : Fin n) : ℝ≥0 := ⟨(a * l ^ (j : ℕ)) ^ 2, sq_nonneg _⟩
  have hb (j : Fin n) : ∀ᵐ u ∂signLaw (a * l ^ (j : ℕ)), |u| ≤ ε * r := by
    filter_upwards [signLaw_bound (a * l ^ (j : ℕ))] with u hu
    apply hu.trans
    rw [abs_of_nonneg (mul_nonneg ha (pow_nonneg hl0 _))]
    exact (mul_le_of_le_one_right ha (pow_le_one₀ hl0 hl1.le)).trans haε
  have hh := Gaussian.detail_finiteConvolution_le (fun j : Fin n ↦ signLaw (a * l ^ (j : ℕ))) v
    hε hε1 hr hb (fun j ↦ signLaw_mean _) (fun j ↦ signLaw_secondMoment _)
  have he : ((∑ j, v j : ℝ≥0) : ℝ) = ∑ j : Fin n, (a * l ^ (j : ℕ)) ^ 2 :=
    NNReal.coe_sum Finset.univ v
  rw [he] at hh
  exact hh

lemma detail_le_scaled_tail {l r : ℝ} (hl : |l| < 1) (hr : 0 < r) (n : ℕ) :
    Gaussian.detail (convolution l) r ≤
      Gaussian.detail ((convolution l).map (fun x ↦ l ^ n * x)) r := by
  conv_lhs => rw [convolution_prefix_tail hl n]
  haveI : IsProbabilityMeasure ((convolution l).map (fun x ↦ l ^ n * x)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  exact Gaussian.detail_conv_le_right _ _ hr

end LpSelfSimilar.Bernoulli
