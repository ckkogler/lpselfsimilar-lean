module

public import LpSelfSimilar.Bernoulli.Decomposition
public import LpSelfSimilar.Bernoulli.FiniteLaw

@[expose] public section

/-!
Exact decomposition at an arbitrary digit index. The finite prefix and infinite
tail use disjoint independent coordinates; the tail is a scaled copy of the
original Bernoulli convolution. This justifies discarding large digits when
estimating Gaussian detail.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Topology

namespace LpSelfSimilar.Bernoulli

lemma tendsto_digitSum {r : ℝ} (hr : |r| < 1) (w : ℕ → Bool) :
    Tendsto (fun n ↦ digitSum r (fun j : Fin n ↦ w j)) atTop (𝓝 (series r w)) := by
  have h := (summable_sign_mul_pow hr w).hasSum.tendsto_sum_nat
  have he (n : ℕ) : digitSum r (fun j : Fin n ↦ w j) =
      ∑ j ∈ Finset.range n, sign (w j) * r ^ j := by
    exact Fin.sum_univ_eq_sum_range (fun j ↦ sign (w j) * r ^ j) n
  simp_rw [he]
  exact h

lemma series_eq_prefix_add_tail {r : ℝ} (hr : |r| < 1) (n : ℕ) (w : ℕ → Bool) :
    series r w = digitSum r (fun j : Fin n ↦ w j) +
      r ^ n * series r (fun j ↦ w (j + n)) := by
  rw [series, ← (summable_sign_mul_pow hr w).sum_add_tsum_nat_add n]
  have he : digitSum r (fun j : Fin n ↦ w j) =
      ∑ j ∈ Finset.range n, sign (w j) * r ^ j :=
    Fin.sum_univ_eq_sum_range (fun j ↦ sign (w j) * r ^ j) n
  rw [he]
  congr 1
  rw [series, ← tsum_mul_left]
  apply tsum_congr
  intro j
  rw [pow_add]
  ring

lemma convolution_prefix_tail {r : ℝ} (hr : |r| < 1) (n : ℕ) :
    convolution r = (digitPMF r n).toMeasure ∗
      ((convolution r).map (fun x ↦ r ^ n * x)) := by
  have hi := independent_subsequences (fun j : Fin n ↦ (j : ℕ)) (fun j : ℕ ↦ j + n) (by
    rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ ⟨j, hj⟩
    change j + n = (i : ℕ) at hj
    have := i.isLt
    omega)
  have hind := hi.comp (measurable_of_countable (digitSum r))
    ((measurable_series r).const_mul (r ^ n))
  have he : series r = (fun w ↦ digitSum r (fun j : Fin n ↦ w j)) +
      (fun w ↦ r ^ n * series r (fun j ↦ w (j + n))) :=
    funext (series_eq_prefix_add_tail hr n)
  change IndepFun (fun w ↦ digitSum r (fun j : Fin n ↦ w j))
    (fun w ↦ r ^ n * series r (fun j ↦ w (j + n))) digitSpace at hind
  conv_lhs => rw [convolution, he, hind.map_add_eq_map_conv_map (by fun_prop) (by fun_prop), digitSum_law]
  congr 1
  have hl := series_subsequence_law r (f := fun j ↦ j + n) (by intro i j h; change i + n = j + n at h; omega)
  rw [← hl, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end LpSelfSimilar.Bernoulli
