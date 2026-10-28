module

public import LpSelfSimilar.Entropy.SupportedJointCancellation
public import LpSelfSimilar.Entropy.FiniteCancellationBounds
public import LpSelfSimilar.Entropy.MeasurableBandConditionals

@[expose] public section

/-!
# Measurability and range of expected conditional cancellation

Conditional vectors vanish outside their allowed supports. Each positive column
is a probability vector; a null column contributes zero to the expectation.
Thus the expected cancellation lies in the same exact interval as the individual
sixteen-point cancellations, independently of the number of labels.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Restrict any zero-preserving function of a conditional vector to its allowed support. -/
theorem supportedJoint_sum_conditional_on_cover {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (j : κ) (F : ℝ → ℝ) (hF : F 0 = 0) :
    (∑ i ∈ cover j, F (jointConditionalWeight u j i)) =
      ∑ i, F (jointConditionalWeight u j i) := by
  classical
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i hi hin
  rw [jointConditionalWeight_eq_zero_of_not_mem p cover hu hin, hF]

/-- Zero coordinates outside the allowed support do not change cancellation. -/
theorem supportedJoint_conditionalCancellation_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (j : κ) :
    finiteCancellation (cover j) (jointConditionalWeight u j) =
      finiteCancellation Finset.univ (jointConditionalWeight u j) := by
  unfold finiteCancellation
  rw [supportedJoint_sum_conditional_on_cover p cover hu j (fun x ↦ x ^ 2) (by simp)]

/-- Expected cancellation is nonnegative for any nonnegative finite joint array. -/
theorem jointExpectedCancellation_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) : 0 ≤ jointExpectedCancellation u := by
  unfold jointExpectedCancellation
  apply Finset.sum_nonneg
  intro j hj
  by_cases hq : jointLabelWeight u j = 0
  · simp [hq]
  have hqpos : 0 < jointLabelWeight u j :=
    lt_of_le_of_ne (jointLabelWeight_nonneg u hu j) (by intro he; exact hq he.symm)
  exact mul_nonneg hqpos.le (finiteCancellation_nonneg Finset.univ
    (jointConditionalWeight u j) (fun i _ ↦ jointConditionalWeight_nonneg u hu j i)
    (sum_jointConditionalWeight_eq_one u j hqpos))

/-- The exact uniform upper bound survives averaging, including all null labels. -/
theorem jointExpectedCancellation_le_sixteen_atom_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] (p : ι → ℝ) (cover : κ → Finset ι)
    {u : ι → κ → ℝ} (hu : u ∈ supportedJointSpace p cover)
    (hsum : ∑ i, p i = 1) (hcard : ∀ j, (cover j).card ≤ 16) :
    jointExpectedCancellation u ≤ 1 - Real.sqrt (7 / 16) := by
  have hcol (j : κ) : jointLabelWeight u j *
      finiteCancellation Finset.univ (jointConditionalWeight u j) ≤
      jointLabelWeight u j * (1 - Real.sqrt (7 / 16)) := by
    by_cases hq : jointLabelWeight u j = 0
    · simp [hq]
    have hqpos : 0 < jointLabelWeight u j :=
      lt_of_le_of_ne (jointLabelWeight_nonneg u hu.1 j) (by intro he; exact hq he.symm)
    have hnorm : ∑ i ∈ cover j, jointConditionalWeight u j i = 1 := by
      rw [supportedJoint_sum_conditional_on_cover p cover hu j (fun x ↦ x) rfl]
      exact sum_jointConditionalWeight_eq_one u j hqpos
    rw [← supportedJoint_conditionalCancellation_eq p cover hu j]
    exact mul_le_mul_of_nonneg_left (finiteCancellation_le_sixteen_atom_bound
      (cover j) (jointConditionalWeight u j) hnorm (hcard j)) hqpos.le
  calc
    jointExpectedCancellation u ≤ ∑ j, jointLabelWeight u j * (1 - Real.sqrt (7 / 16)) :=
      Finset.sum_le_sum (fun j _ ↦ hcol j)
    _ = 1 - Real.sqrt (7 / 16) := by
      rw [← Finset.sum_mul, sum_jointLabelWeight_eq_one p cover hu hsum, one_mul]

/-- Expected cancellation is measurable for a measurable family of finite joint arrays. -/
theorem measurable_jointExpectedCancellation {ι κ Ω : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace Ω] {u : Ω → ι → κ → ℝ} (hu : Measurable u) :
    Measurable (fun x ↦ jointExpectedCancellation (u x)) := by
  unfold jointExpectedCancellation finiteCancellation jointConditionalWeight jointLabelWeight
  fun_prop

end LpSelfSimilar.Entropy
