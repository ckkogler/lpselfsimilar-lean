module

public import LpSelfSimilar.Entropy.FiniteVariational

@[expose] public section

/-!
# Finite conditional laws from weighted covers

Given weights on a family of finite sets, a point chooses a label among the
sets containing it, in proportion to those weights. Dividing by the point's
actual coverage normalizes this conditional choice. The resulting joint law
has exactly the prescribed point marginal, including zero-probability points.
This is the finite construction used with independent sets of a complement graph.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Total weight of labels whose finite set contains the given point. -/
noncomputable def finiteCoverWeight {ι κ : Type*} (t : Finset κ)
    (w : κ → ℝ) (cover : κ → Finset ι) (i : ι) : ℝ := by
  classical
  exact ∑ j ∈ t, if i ∈ cover j then w j else 0

/-- Joint point/label weight for coverage-normalized sampling of a label. -/
noncomputable def finiteCoverJoint {ι κ : Type*} (t : Finset κ) (p : ι → ℝ)
    (w : κ → ℝ) (cover : κ → Finset ι) (i : ι) (j : κ) : ℝ := by
  classical
  exact p i * (if i ∈ cover j then w j else 0) / finiteCoverWeight t w cover i

lemma finiteCoverWeight_nonneg {ι κ : Type*} (t : Finset κ)
    (w : κ → ℝ) (cover : κ → Finset ι) (hw : ∀ j ∈ t, 0 ≤ w j) (i : ι) :
    0 ≤ finiteCoverWeight t w cover i := by
  classical
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact hw j hj
  · exact le_rfl

lemma finiteCoverJoint_nonneg {ι κ : Type*} (t : Finset κ) (p : ι → ℝ)
    (w : κ → ℝ) (cover : κ → Finset ι) {i : ι} {j : κ}
    (hp : 0 ≤ p i) (hw : ∀ k ∈ t, 0 ≤ w k) (hj : j ∈ t) :
    0 ≤ finiteCoverJoint t p w cover i j := by
  classical
  have hc := finiteCoverWeight_nonneg t w cover hw i
  have hweight : 0 ≤ (if i ∈ cover j then w j else 0) := by
    split_ifs
    · exact hw j hj
    · exact le_rfl
  exact div_nonneg (mul_nonneg hp hweight) hc

/-- Positive joint mass is supported on the set attached to its label. -/
lemma finiteCoverJoint_eq_zero_of_not_mem {ι κ : Type*} (t : Finset κ)
    (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι) {i : ι} {j : κ}
    (hnot : i ∉ cover j) : finiteCoverJoint t p w cover i j = 0 := by
  classical
  simp [finiteCoverJoint, hnot]

/-- The point marginal is unchanged; zero-mass points need no positive coverage. -/
theorem sum_finiteCoverJoint_eq {ι κ : Type*} (t : Finset κ) (p : ι → ℝ)
    (w : κ → ℝ) (cover : κ → Finset ι) (i : ι)
    (hc : p i ≠ 0 → 0 < finiteCoverWeight t w cover i) :
    ∑ j ∈ t, finiteCoverJoint t p w cover i j = p i := by
  classical
  by_cases hp : p i = 0
  · simp [finiteCoverJoint, hp]
  · simp only [finiteCoverJoint]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    exact mul_div_cancel_right₀ _ (hc hp).ne'

/-- Joint weights sum to one. Nonnegativity is proved separately above. The label
weights need not sum to one; only coverage of every positive-mass point matters. -/
theorem sum_sum_finiteCoverJoint_eq_one {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι)
    (hsum : ∑ i ∈ s, p i = 1)
    (hc : ∀ i ∈ s, p i ≠ 0 → 0 < finiteCoverWeight t w cover i) :
    ∑ i ∈ s, ∑ j ∈ t, finiteCoverJoint t p w cover i j = 1 := by
  calc
    _ = ∑ i ∈ s, p i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact sum_finiteCoverJoint_eq t p w cover i (hc i hi)
    _ = 1 := hsum

end LpSelfSimilar.Entropy
