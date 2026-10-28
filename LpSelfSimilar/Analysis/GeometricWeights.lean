module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic

@[expose] public section

/-!
# Geometric interval weights and squared lengths

The weights `(1-theta)*theta^k` are the lengths between successive geometric
endpoints. Their finite sum plus the last tail is exactly one. The sum of their
squares is at most `(1-theta)/(1+theta)`, with no infinite-series interchange.
-/

open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- The finite geometric weights and the remaining tail have total mass one. -/
theorem sum_geometric_weights_add_tail (θ : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (1 - θ) * θ ^ k) + θ ^ N = 1 := by
  rw [← Finset.mul_sum]
  have h := geom_sum_mul_neg θ N
  nlinarith

/-- The squared lengths of finitely many geometric intervals have the sharp uniform bound. -/
theorem sum_sq_geometric_gaps_le {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (N : ℕ) :
    ∑ k ∈ Finset.range N, (θ ^ k - θ ^ (k + 1)) ^ 2 ≤ (1 - θ) / (1 + θ) := by
  have hden : 0 < 1 - θ ^ 2 := by nlinarith
  have hplus : 0 < 1 + θ := by linarith
  have hgeom := geom_sum_mul_neg (θ ^ 2) N
  have hsum : (∑ k ∈ Finset.range N, (θ ^ 2) ^ k) ≤ 1 / (1 - θ ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [pow_nonneg (sq_nonneg θ) N]
  calc
    (∑ k ∈ Finset.range N, (θ ^ k - θ ^ (k + 1)) ^ 2) =
        (1 - θ) ^ 2 * ∑ k ∈ Finset.range N, (θ ^ 2) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have he : (θ ^ 2) ^ k = (θ ^ k) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 k]
      rw [he, pow_succ]
      ring
    _ ≤ (1 - θ) ^ 2 * (1 / (1 - θ ^ 2)) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (1 - θ) / (1 + θ) := by
      field_simp
      <;> ring

/-- The `N` geometric interval masses together with the final tail, on `N+1` labels. -/
noncomputable def geometricWeight (θ : ℝ) (N : ℕ) (k : Fin (N + 1)) : ℝ :=
  if (k : ℕ) < N then (1 - θ) * θ ^ (k : ℕ) else θ ^ N

/-- Expanding a weighted sum separates the original geometric labels and the final tail. -/
theorem sum_geometricWeight_mul (θ : ℝ) (N : ℕ) (f : ℕ → ℝ) :
    (∑ k : Fin (N + 1), geometricWeight θ N k * f k) =
      (∑ k ∈ Finset.range N, (1 - θ) * θ ^ k * f k) + θ ^ N * f N := by
  rw [Fin.sum_univ_castSucc]
  simp only [geometricWeight, Fin.val_castSucc, Fin.is_lt, ite_true, Fin.val_last,
    lt_self_iff_false, ite_false]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ (1 - θ) * θ ^ k * f k) N]

/-- The finite geometric weights are nonnegative in the contracting range. -/
theorem geometricWeight_nonneg {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (N : ℕ) (k : Fin (N + 1)) : 0 ≤ geometricWeight θ N k := by
  unfold geometricWeight
  split_ifs
  · exact mul_nonneg (sub_nonneg.mpr hθ1) (pow_nonneg hθ0 _)
  · exact pow_nonneg hθ0 _

/-- The finite geometric weight vector is a probability vector. -/
theorem sum_geometricWeight_eq_one (θ : ℝ) (N : ℕ) :
    ∑ k : Fin (N + 1), geometricWeight θ N k = 1 := by
  simpa only [mul_one] using (sum_geometricWeight_mul θ N (fun _ ↦ 1)).trans
    (by simpa only [mul_one] using sum_geometric_weights_add_tail θ N)

end LpSelfSimilar.Analysis
