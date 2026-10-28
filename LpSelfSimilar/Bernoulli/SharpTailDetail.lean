module

public import LpSelfSimilar.Bernoulli.TailDetail
public import LpSelfSimilar.Gaussian.SharpSmallSummands

@[expose] public section

/-!
The explicit replacement bound for infinite Bernoulli tails. Dominated convergence
for smoothed derivatives and Fatou's lemma transfer the checked finite estimate
with constant fifteen to the actual infinite series law.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Filter
open scoped Topology NNReal

namespace LpSelfSimilar.Bernoulli

/-- An infinite tail obeys the same finite small-summand bound. -/
theorem detail_scaled_convolution_le_fifteen {l a ε r : ℝ}
    (hl0 : 0 ≤ l) (hl1 : l < 1) (ha : 0 ≤ a)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hr : 0 < r) (haε : a ≤ ε * r) :
    Gaussian.detail ((convolution l).map (fun x ↦ a * x)) r ≤
      r ^ 2 / (r ^ 2 + a ^ 2 / (1 - l ^ 2)) + 15 * ε := by
  have hlabs : |l| < 1 := by simpa only [abs_of_nonneg hl0] using hl1
  have hlsq : l ^ 2 < 1 := by nlinarith
  have hvar : 0 ≤ a ^ 2 / (1 - l ^ 2) := by positivity
  have hd : r ^ 2 + a ^ 2 / (1 - l ^ 2) ≠ 0 := by positivity
  have hC : Tendsto (fun n ↦ r ^ 2 / (r ^ 2 + ∑ j : Fin n, (a * l ^ (j : ℕ)) ^ 2) +
      15 * ε) atTop
      (𝓝 (r ^ 2 / (r ^ 2 + a ^ 2 / (1 - l ^ 2)) + 15 * ε)) :=
    (tendsto_const_nhds.div (tendsto_const_nhds.add
    (tendsto_prefix_variance hl0 hl1 a)) hd).add_const (15 * ε)
  have hme : (convolution l).map (fun x ↦ a * x) = digitSpace.map (fun w ↦ a * series l w) := by
    rw [convolution, Measure.map_map (by fun_prop) (measurable_series l)]
    rfl
  rw [hme]
  apply Gaussian.detail_map_le_of_tendsto digitSpace
    (fun n ↦ by fun_prop) (by fun_prop)
    (ae_of_all _ (fun w ↦ tendsto_const_nhds.mul (tendsto_digitSum hlabs w))) hr
    (by positivity) hC
  intro n
  rw [scaled_prefix_law]
  let v (j : Fin n) : ℝ≥0 := ⟨(a * l ^ (j : ℕ)) ^ 2, sq_nonneg _⟩
  have hb (j : Fin n) : ∀ᵐ u ∂signLaw (a * l ^ (j : ℕ)), |u| ≤ ε * r := by
    filter_upwards [signLaw_bound (a * l ^ (j : ℕ))] with u hu
    apply hu.trans
    rw [abs_of_nonneg (mul_nonneg ha (pow_nonneg hl0 _))]
    exact (mul_le_of_le_one_right ha (pow_le_one₀ hl0 hl1.le)).trans haε
  have hh := Gaussian.detail_finiteConvolution_le_fifteen (fun j : Fin n ↦ signLaw (a * l ^ (j : ℕ))) v
    hε hε1 hr hb (fun j ↦ signLaw_mean _) (fun j ↦ signLaw_secondMoment _)
  have he : ((∑ j, v j : ℝ≥0) : ℝ) = ∑ j : Fin n, (a * l ^ (j : ℕ)) ^ 2 :=
    NNReal.coe_sum Finset.univ v
  rw [he] at hh
  exact hh

end LpSelfSimilar.Bernoulli
