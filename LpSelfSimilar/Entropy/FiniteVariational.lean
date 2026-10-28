module

public import LpSelfSimilar.Entropy.Bounds

@[expose] public section

/-!
# Finite entropy variational bounds

The elementary inequality `log u ≤ u - 1` gives the Gibbs variational bound
for a finite probability vector. Zero-probability atoms are included explicitly;
the comparison weights must be positive but need only have total mass at most
one. Entropy uses natural logarithms in this module.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

lemma negMulLog_le_cross_entropy_term {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    Real.negMulLog x ≤ x * (-Real.log q) + q - x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simpa using hq.le
  · have h := negMulLog_le_log_bound hx (inv_pos.mpr hq)
    simpa only [Real.log_inv, one_div, inv_inv] using h

/-- Gibbs' inequality for a subprobability comparison vector. -/
theorem finite_entropy_le_cross_entropy {ι : Type*} (s : Finset ι)
    (p q : ι → ℝ) (hp : ∀ j ∈ s, 0 ≤ p j) (hsum : ∑ j ∈ s, p j = 1)
    (hq : ∀ j ∈ s, 0 < q j) (hqsum : ∑ j ∈ s, q j ≤ 1) :
    ∑ j ∈ s, Real.negMulLog (p j) ≤ ∑ j ∈ s, p j * (-Real.log (q j)) := by
  have h := Finset.sum_le_sum (fun j hj ↦ negMulLog_le_cross_entropy_term (hp j hj) (hq j hj))
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum] at h
  linarith

/-- The log-partition variational inequality, with arbitrary positive weights. -/
theorem finite_entropy_le_log_partition {ι : Type*} (s : Finset ι)
    (p w : ι → ℝ) (hp : ∀ j ∈ s, 0 ≤ p j) (hsum : ∑ j ∈ s, p j = 1)
    (hw : ∀ j ∈ s, 0 < w j) {Z : ℝ} (hZ : 0 < Z)
    (hwZ : ∑ j ∈ s, w j ≤ Z) :
    ∑ j ∈ s, Real.negMulLog (p j) ≤
      Real.log Z - ∑ j ∈ s, p j * Real.log (w j) := by
  have h := finite_entropy_le_cross_entropy s p (fun j ↦ w j / Z) hp hsum
    (fun j hj ↦ div_pos (hw j hj) hZ) (by
      rw [← Finset.sum_div]
      exact (div_le_one hZ).mpr hwZ)
  calc
    _ ≤ ∑ j ∈ s, p j * (-Real.log (w j / Z)) := h
    _ = ∑ j ∈ s, (p j * Real.log Z - p j * Real.log (w j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Real.log_div (hw j hj).ne' hZ.ne']
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]

/-- Assign one distinguished atom weight one and each remaining atom `exp (-t)`.
This is the binary-entropy variational estimate with at most `N` other atoms. -/
theorem finite_entropy_le_dominant_atom_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (p : ι → ℝ) (i : ι) (hi : i ∈ s)
    (hp : ∀ j ∈ s, 0 ≤ p j) (hsum : ∑ j ∈ s, p j = 1)
    (N : ℕ) (hcard : (s.erase i).card ≤ N) (t : ℝ) :
    ∑ j ∈ s, Real.negMulLog (p j) ≤
      t * (1 - p i) + Real.log (1 + N * Real.exp (-t)) := by
  let w : ι → ℝ := fun j ↦ if j = i then 1 else Real.exp (-t)
  have hw : ∀ j ∈ s, 0 < w j := by
    intro j _
    simp only [w]
    split_ifs <;> positivity
  have hsumw : ∑ j ∈ s, w j = 1 + (s.erase i).card * Real.exp (-t) := by
    rw [← Finset.sum_erase_add s w hi]
    have he : ∑ j ∈ s.erase i, w j = (s.erase i).card * Real.exp (-t) := by
      calc
        _ = ∑ _j ∈ s.erase i, Real.exp (-t) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [w, Finset.ne_of_mem_erase hj]
        _ = _ := by simp
    rw [he]
    simp [w, add_comm]
  have h := finite_entropy_le_log_partition s p w hp hsum hw
    (Z := 1 + N * Real.exp (-t)) (by positivity) (by
      rw [hsumw]
      have hc : ((s.erase i).card : ℝ) ≤ N := by exact_mod_cast hcard
      gcongr)
  have hrest : ∑ j ∈ s.erase i, p j = 1 - p i := by
    have he := Finset.sum_erase_add s p hi
    rw [hsum] at he
    linarith
  have he : ∑ j ∈ s, p j * Real.log (w j) = -t * (1 - p i) := by
    rw [← Finset.sum_erase_add s (fun j ↦ p j * Real.log (w j)) hi]
    have he' : ∑ j ∈ s.erase i, p j * Real.log (w j) =
        (∑ j ∈ s.erase i, p j) * (-t) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      simp [w, Finset.ne_of_mem_erase hj]
    rw [he', hrest]
    simp [w, mul_comm]
  rw [he] at h
  linarith

end LpSelfSimilar.Entropy
