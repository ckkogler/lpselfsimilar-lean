module

public import LpSelfSimilar.Entropy.SixteenAtomCancellation

@[expose] public section

/-!
# Range of the finite cancellation functional

For a probability vector the functional is nonnegative. With at most sixteen
atoms it is at most `1 - sqrt (7/16)`. The lower collision bound comes from
Cauchy--Schwarz and uses the actual support cardinality.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

lemma finiteCancellation_nonneg {ι : Type*}
    (s : Finset ι) (p : ι → ℝ) (hp : ∀ j ∈ s, 0 ≤ p j)
    (hsum : ∑ j ∈ s, p j = 1) : 0 ≤ finiteCancellation s p := by
  classical
  have hC0 : 0 ≤ ∑ j ∈ s, (p j) ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hC1 : ∑ j ∈ s, (p j) ^ 2 ≤ 1 := by
    rw [← hsum]
    apply Finset.sum_le_sum
    intro j hj
    have hmax : p j ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum hp hj
    nlinarith [hp j hj]
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 / 5 + (3 / 5) * ∑ j ∈ s, (p j) ^ 2)
  have hnonneg := Real.sqrt_nonneg (2 / 5 + (3 / 5) * ∑ j ∈ s, (p j) ^ 2)
  dsimp [finiteCancellation]
  nlinarith

lemma finiteCancellation_le_sixteen_atom_bound {ι : Type*}
    (s : Finset ι) (p : ι → ℝ) (hsum : ∑ j ∈ s, p j = 1)
    (hcard : s.card ≤ 16) : finiteCancellation s p ≤ 1 - Real.sqrt (7 / 16) := by
  have hC0 : 0 ≤ ∑ j ∈ s, (p j) ^ 2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have h := Finset.sum_mul_sq_le_sq_mul_sq s p (fun _ ↦ (1 : ℝ))
  simp only [mul_one, hsum, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hc : (s.card : ℝ) ≤ 16 := by exact_mod_cast hcard
  have hm := mul_le_mul_of_nonneg_left hc hC0
  have hlow : 7 / 16 ≤ 2 / 5 + (3 / 5) * ∑ j ∈ s, (p j) ^ 2 := by nlinarith
  have hsqrt := Real.sqrt_le_sqrt hlow
  dsimp [finiteCancellation]
  linarith

end LpSelfSimilar.Entropy
