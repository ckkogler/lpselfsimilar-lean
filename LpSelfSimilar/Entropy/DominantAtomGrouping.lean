module

public import LpSelfSimilar.Entropy.BinaryVariational

@[expose] public section

/-!
# Grouping the nondominant atoms in finite entropy

A family with total mass delta and at most N entries has entropy at most
-delta*log(delta)+delta*log(N). This statement includes delta=0 and zero
individual weights. Applying it after deleting a distinguished atom gives
binary entropy of the outside mass plus its logarithmic cardinality cost.
At sixteen atoms the cost is exactly delta*log(15).
-/

open Real
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- The exact entropy bound at arbitrary nonnegative total mass. -/
theorem finite_entropy_mass_bound {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ j ∈ s, 0 ≤ p j) {δ N : ℝ} (hsum : ∑ j ∈ s, p j = δ)
    (hN : 0 < N) (hcard : (s.card : ℝ) ≤ N) :
    ∑ j ∈ s, negMulLog (p j) ≤ negMulLog δ + δ * log N := by
  have hδ : 0 ≤ δ := hsum ▸ Finset.sum_nonneg hp
  rcases eq_or_lt_of_le hδ with rfl | hδ
  · have hz := (Finset.sum_eq_zero_iff_of_nonneg hp).mp hsum
    have he : ∑ j ∈ s, negMulLog (p j) = 0 :=
      Finset.sum_eq_zero (fun j hj => by rw [hz j hj, negMulLog_zero])
    simp [he]
  · have h := Finset.sum_le_sum (fun j hj =>
      negMulLog_le_cross_entropy_term (hp j hj) (div_pos hδ hN))
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      hsum, Finset.sum_const, nsmul_eq_mul] at h
    have hc : (s.card : ℝ) * (δ / N) ≤ δ := by
      calc
        _ ≤ N * (δ / N) := mul_le_mul_of_nonneg_right hcard (div_nonneg hδ.le hN.le)
        _ = δ := by field_simp
    rw [log_div hδ.ne' hN.ne'] at h
    dsimp [negMulLog] at h ⊢
    nlinarith

/-- Grouping every atom except a distinguished one gives the exact binary-entropy bound. -/
theorem finite_entropy_le_binary_grouping {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (i : ι) (hi : i ∈ s)
    (hp : ∀ j ∈ s, 0 ≤ p j) (hsum : ∑ j ∈ s, p j = 1)
    {N : ℝ} (hN : 0 < N) (hcard : ((s.erase i).card : ℝ) ≤ N) :
    ∑ j ∈ s, negMulLog (p j) ≤ binEntropy (1 - p i) + (1 - p i) * log N := by
  have hrest : ∑ j ∈ s.erase i, p j = 1 - p i := by
    have h := Finset.sum_erase_add s p hi
    rw [hsum] at h
    linarith
  have h := finite_entropy_mass_bound (s.erase i) p
    (fun j hj => hp j (Finset.mem_of_mem_erase hj)) hrest hN hcard
  have he := Finset.sum_erase_add s (fun j => negMulLog (p j)) hi
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub, sub_sub_cancel]
  linarith

/-- At most sixteen atoms leave at most fifteen alternatives after grouping. -/
theorem sixteen_atom_entropy_le_binary_grouping {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (i : ι) (hi : i ∈ s)
    (hp : ∀ j ∈ s, 0 ≤ p j) (hsum : ∑ j ∈ s, p j = 1) (hcard : s.card ≤ 16) :
    (∑ j ∈ s, negMulLog (p j)) / log 2 ≤
      binEntropy (1 - p i) / log 2 + (1 - p i) * (log 15 / log 2) := by
  have hc : (s.erase i).card ≤ 15 := by
    rw [Finset.card_erase_of_mem hi]
    omega
  have h := finite_entropy_le_binary_grouping s p i hi hp hsum
    (by norm_num : (0 : ℝ) < 15) (by exact_mod_cast hc)
  have hdiv := div_le_div_of_nonneg_right h (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  simpa only [add_div, mul_div_assoc] using hdiv

end LpSelfSimilar.Entropy
