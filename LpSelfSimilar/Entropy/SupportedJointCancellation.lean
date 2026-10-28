module

public import LpSelfSimilar.Entropy.SupportedJointConditionals
public import LpSelfSimilar.Entropy.SixteenAtomCancellation

@[expose] public section

/-!
# Expected entropy and cancellation of supported joint laws

Apply the sixteen-atom inequality separately to each positive-mass conditional
vector and average. Null labels contribute zero without a normalization
assumption. The averaged cancellation is computed from all point coordinates;
coordinates outside the allowed cover vanish exactly.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Expected finite cancellation of the conditional point vectors of a joint law. -/
noncomputable def jointExpectedCancellation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → κ → ℝ) : ℝ :=
  ∑ j, jointLabelWeight u j * finiteCancellation Finset.univ (jointConditionalWeight u j)

/-- For conditional supports of size at most sixteen, the exact entropy-cancellation bound averages. -/
theorem supportedJoint_entropy_le_expected_cancellation {ι κ : Type*}
    [Fintype ι] [Fintype κ] (p : ι → ℝ) (cover : κ → Finset ι)
    {u : ι → κ → ℝ} (hu : u ∈ supportedJointSpace p cover)
    (hsum : ∑ i, p i = 1) (hcard : ∀ j, (cover j).card ≤ 16)
    {α : ℝ} (hα : 0 < α) :
    jointConditionalEntropy u / Real.log 2 ≤ α * jointExpectedCancellation u +
      Real.log (1 + 15 * (2 : ℝ) ^ (-α * (13 / 40 : ℝ))) / Real.log 2 := by
  classical
  let R := Real.log (1 + 15 * (2 : ℝ) ^ (-α * (13 / 40 : ℝ))) / Real.log 2
  have hcol (j : κ) :
      jointLabelWeight u j * ((∑ i, Real.negMulLog (jointConditionalWeight u j i)) / Real.log 2) ≤
        jointLabelWeight u j * (α * finiteCancellation Finset.univ (jointConditionalWeight u j) + R) := by
    by_cases hq : jointLabelWeight u j = 0
    · simp [hq]
    have hqpos : 0 < jointLabelWeight u j :=
      lt_of_le_of_ne (jointLabelWeight_nonneg u hu.1 j) (by intro he; exact hq he.symm)
    have hz (i : ι) (hi : i ∉ cover j) : jointConditionalWeight u j i = 0 :=
      jointConditionalWeight_eq_zero_of_not_mem p cover hu hi
    have hrestrict (F : ℝ → ℝ) (hF : F 0 = 0) :
        (∑ i ∈ cover j, F (jointConditionalWeight u j i)) =
          ∑ i, F (jointConditionalWeight u j i) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i hi hin
      rw [hz i hin, hF]
    have hnorm : ∑ i ∈ cover j, jointConditionalWeight u j i = 1 := by
      rw [hrestrict (fun x ↦ x) rfl]
      exact sum_jointConditionalWeight_eq_one u j hqpos
    have h := sixteen_atom_entropy_le_cancellation (cover j) (jointConditionalWeight u j)
      (fun i _ ↦ jointConditionalWeight_nonneg u hu.1 j i) hnorm (hcard j) hα
    rw [hrestrict Real.negMulLog (by simp)] at h
    have he : finiteCancellation (cover j) (jointConditionalWeight u j) =
        finiteCancellation Finset.univ (jointConditionalWeight u j) := by
      unfold finiteCancellation
      rw [hrestrict (fun x ↦ x ^ 2) (by simp)]
    rw [he] at h
    exact mul_le_mul_of_nonneg_left h hqpos.le
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hcol j)
  have he : (∑ j, jointLabelWeight u j *
      (α * finiteCancellation Finset.univ (jointConditionalWeight u j) + R)) =
      α * jointExpectedCancellation u + R := by
    unfold jointExpectedCancellation
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      sum_jointLabelWeight_eq_one p cover hu hsum, one_mul]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he] at h
  rw [jointConditionalEntropy_eq_labelWeight_entropy u hu.1]
  simpa only [Finset.sum_div, mul_div_assoc] using h

end LpSelfSimilar.Entropy
