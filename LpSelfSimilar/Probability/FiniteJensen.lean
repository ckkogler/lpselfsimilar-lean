module

public import LpSelfSimilar.Probability.FiniteMoments

@[expose] public section

/-!
Finite Jensen inequalities for square roots and fourth roots. The weights need
only be nonnegative and sum to one, so zero-mass atoms require no reduction.
-/

namespace LpSelfSimilar

lemma weighted_sqrt_le_sqrt_weighted {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, w i * Real.sqrt (x i)) ≤ Real.sqrt (∑ i, w i * x i) := by
  classical
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i ↦ w i * Real.sqrt (x i)) (f := w) (g := fun i ↦ w i * x i)
    (fun i _ ↦ hw i) (fun i _ ↦ mul_nonneg (hw i) (hx i))
    (fun i _ ↦ by rw [mul_pow, Real.sq_sqrt (hx i)]; ring_nf; exact le_rfl)
  rw [hsum, one_mul] at h
  have hn : 0 ≤ ∑ i, w i * x i := Finset.sum_nonneg (fun i _ ↦ mul_nonneg (hw i) (hx i))
  nlinarith [Real.sq_sqrt hn, Real.sqrt_nonneg (∑ i, w i * x i)]

lemma weighted_fourthRoot_le_fourthRoot_weighted {ι : Type*} [Fintype ι]
    (w x : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hx : ∀ i, 0 ≤ x i) :
    (∑ i, w i * Real.sqrt (Real.sqrt (x i))) ≤
      Real.sqrt (Real.sqrt (∑ i, w i * x i)) :=
  (weighted_sqrt_le_sqrt_weighted w (fun i ↦ Real.sqrt (x i)) hw hsum
    (fun i ↦ Real.sqrt_nonneg _)).trans
      (Real.sqrt_le_sqrt (weighted_sqrt_le_sqrt_weighted w x hw hsum hx))

end LpSelfSimilar
