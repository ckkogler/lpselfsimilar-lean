module

public import LpSelfSimilar.Bernoulli.FiniteLaw

@[expose] public section

/-!
Uniform support bounds for every finite digit block. These bounds are independent
of block length, and provide the large-scale endpoint for the entropy argument.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Bernoulli

lemma abs_digitSum_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {n : ℕ} (w : Fin n → Bool) : |digitSum r w| ≤ (1 - r)⁻¹ := by
  calc
    |digitSum r w| ≤ ∑ j : Fin n, |sign (w j) * r ^ (j : ℕ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin n, r ^ (j : ℕ) := by
      simp [abs_mul, abs_pow, abs_of_nonneg hr0]
    _ = ∑ j ∈ Finset.range n, r ^ j := Fin.sum_univ_eq_sum_range _ _
    _ ≤ ∑' j, r ^ j := (summable_geometric_of_lt_one hr0 hr1).sum_le_tsum
      _ (fun j _ ↦ pow_nonneg hr0 j)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1

lemma digitPMF_support_subset_interval {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (digitPMF r n).support ⊆ Icc (-(1 - r)⁻¹) ((1 - r)⁻¹) := by
  intro x hx
  simp only [digitPMF, PMF.support_map] at hx
  obtain ⟨w, _, rfl⟩ := hx
  exact abs_le.mp (abs_digitSum_le hr0 hr1 w)

end LpSelfSimilar.Bernoulli
