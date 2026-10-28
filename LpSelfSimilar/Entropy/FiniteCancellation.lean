module

public import LpSelfSimilar.Entropy.Collision

@[expose] public section

/-!
# Entropy and cancellation for finite probability vectors

The cancellation functional used in geometric phase averaging is
`1 - sqrt (2/5 + (3/5) * sum p_i^2)`. It controls the mass outside a largest
atom with the explicit coefficient `13/40`. These finite-dimensional estimates
have no arithmetic or Bernoulli-convolution hypotheses.

The proof splits at largest-atom mass `1/2`: below that threshold every atom
is bounded by the largest one; above it, concentrating the remaining mass
in one atom gives a stronger collision bound.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- A scalar form of the cancellation estimate, retaining both collision bounds. -/
lemma cancellation_ge_thirteen_fortieths {δ C : ℝ}
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C)
    (hconcentrated : C ≤ (1 - δ) ^ 2 + δ ^ 2) (hmax : C ≤ 1 - δ) :
    (13 / 40 : ℝ) * δ ≤ 1 - Real.sqrt (2 / 5 + (3 / 5) * C) := by
  have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 / 5 + (3 / 5) * C)
  have hs0 := Real.sqrt_nonneg (2 / 5 + (3 / 5) * C)
  have hbound : 2 / 5 + (3 / 5) * C ≤ (1 - (13 / 40 : ℝ) * δ) ^ 2 := by
    rcases le_total δ (1 / 2) with hsmall | hlarge
    · have hprod := mul_nonneg hδ (sub_nonneg.mpr hsmall)
      nlinarith
    · have hprod := mul_nonneg hδ (sub_nonneg.mpr hlarge)
      nlinarith
  have hright : 0 ≤ 1 - (13 / 40 : ℝ) * δ := by linarith
  nlinarith

/-- The exact `13/40` coefficient for any finite probability vector.
The distinguished index is an actual largest atom, including zero-mass indices. -/
theorem finite_cancellation_ge_mass_outside_max {ι : Type*}
    (s : Finset ι) (p : ι → ℝ) (i : ι) (hi : i ∈ s)
    (hp : ∀ j ∈ s, 0 ≤ p j) (hsum : ∑ j ∈ s, p j = 1)
    (hmax : ∀ j ∈ s, p j ≤ p i) :
    (13 / 40 : ℝ) * (1 - p i) ≤
      1 - Real.sqrt (2 / 5 + (3 / 5) * ∑ j ∈ s, (p j) ^ 2) := by
  classical
  have hpi : p i ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum hp hi
  have hrest : ∑ j ∈ s.erase i, p j = 1 - p i := by
    have h := Finset.sum_erase_add s p hi
    rw [hsum] at h
    linarith
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := s.erase i) (f := p) (fun j hj ↦ hp j (Finset.mem_of_mem_erase hj))
  rw [hrest] at hsq
  have hsplit := Finset.sum_erase_add s (fun j ↦ (p j) ^ 2) hi
  apply cancellation_ge_thirteen_fortieths (sub_nonneg.mpr hpi)
    (by linarith [hp i hi]) (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))
  · nlinarith
  · have h := Finset.sum_le_sum (s := s) (f := fun j ↦ (p j) ^ 2)
      (g := fun j ↦ p j * p i) (fun j hj ↦ by
        nlinarith [mul_le_mul_of_nonneg_left (hmax j hj) (hp j hj)])
    rw [← Finset.sum_mul, hsum, one_mul] at h
    simpa using h

end LpSelfSimilar.Entropy
