module

public import LpSelfSimilar.Entropy.FiniteCover

@[expose] public section

/-!
# Information costs of finite covers

Positive coverage vectors whose coordinatewise product has total mass at most
one give the reverse inequality in complementary graph-entropy duality. The
joint cover construction also has an explicit entropy expansion, retaining
zero-mass points and zero-weight labels without assigning logarithms of ratios
on those null entries.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- The entropy inequality used for complementary independent-set coverages. -/
theorem finite_entropy_le_coverage_cost_add {ι : Type*} (s : Finset ι)
    (p x y : ι → ℝ) (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    (hx : ∀ i ∈ s, 0 < x i) (hy : ∀ i ∈ s, 0 < y i)
    (hxy : ∑ i ∈ s, x i * y i ≤ 1) :
    ∑ i ∈ s, Real.negMulLog (p i) ≤
      (∑ i ∈ s, p i * (-Real.log (x i))) + ∑ i ∈ s, p i * (-Real.log (y i)) := by
  have h := finite_entropy_le_cross_entropy s p (fun i ↦ x i * y i) hp hsum
    (fun i hi ↦ mul_pos (hx i hi) (hy i hi)) hxy
  calc
    _ ≤ ∑ i ∈ s, p i * (-Real.log (x i * y i)) := h
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.log_mul (hx i hi).ne' (hy i hi).ne']
      ring

/-- The actual label marginal of the finite joint construction. -/
noncomputable def finiteCoverLabelWeight {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι) (j : κ) : ℝ :=
  ∑ i ∈ s, finiteCoverJoint t p w cover i j

/-- Pointwise entropy expansion; all null point/label entries are handled explicitly. -/
lemma negMulLog_finiteCoverJoint {ι κ : Type*} (t : Finset κ) (p : ι → ℝ)
    (w : κ → ℝ) (cover : κ → Finset ι) (i : ι) (j : κ)
    (hc : p i ≠ 0 → 0 < finiteCoverWeight t w cover i) :
    Real.negMulLog (finiteCoverJoint t p w cover i j) =
      finiteCoverJoint t p w cover i j *
        (-Real.log (p i) + Real.log (finiteCoverWeight t w cover i)) +
      finiteCoverJoint t p w cover i j * (-Real.log (w j)) := by
  classical
  by_cases hp : p i = 0
  · simp [finiteCoverJoint, hp]
  by_cases hw : w j = 0
  · simp [finiteCoverJoint, hw]
  by_cases hmem : i ∈ cover j
  · simp only [finiteCoverJoint, ite_eq_left hmem]
    rw [Real.negMulLog, Real.log_div (mul_ne_zero hp hw) (hc hp).ne', Real.log_mul hp hw]
    ring
  · simp [finiteCoverJoint, hmem]

/-- Exact joint-entropy identity for normalized cover sampling. -/
theorem finiteCover_joint_entropy_eq {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι)
    (hc : ∀ i ∈ s, p i ≠ 0 → 0 < finiteCoverWeight t w cover i) :
    (∑ i ∈ s, ∑ j ∈ t, Real.negMulLog (finiteCoverJoint t p w cover i j)) =
      (∑ i ∈ s, Real.negMulLog (p i)) +
      (∑ i ∈ s, p i * Real.log (finiteCoverWeight t w cover i)) +
      ∑ j ∈ t, finiteCoverLabelWeight s t p w cover j * (-Real.log (w j)) := by
  have hrow (i : ι) (hi : i ∈ s) :
      (∑ j ∈ t, Real.negMulLog (finiteCoverJoint t p w cover i j)) =
        Real.negMulLog (p i) + p i * Real.log (finiteCoverWeight t w cover i) +
          ∑ j ∈ t, finiteCoverJoint t p w cover i j * (-Real.log (w j)) := by
    calc
      _ = ∑ j ∈ t, (finiteCoverJoint t p w cover i j *
          (-Real.log (p i) + Real.log (finiteCoverWeight t w cover i)) +
          finiteCoverJoint t p w cover i j * (-Real.log (w j))) := by
        apply Finset.sum_congr rfl
        intro j _
        exact negMulLog_finiteCoverJoint t p w cover i j (hc i hi)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul,
          sum_finiteCoverJoint_eq t p w cover i (hc i hi)]
        unfold Real.negMulLog
        ring
  calc
    _ = ∑ i ∈ s, (Real.negMulLog (p i) + p i * Real.log (finiteCoverWeight t w cover i) +
        ∑ j ∈ t, finiteCoverJoint t p w cover i j * (-Real.log (w j))) :=
      Finset.sum_congr rfl hrow
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul]
      rfl

/-- Conditioning on a cover label loses at most the logarithmic coverage cost.
The joint and label entropies are those of the actual constructed finite weights. -/
theorem finiteCover_joint_sub_label_entropy_ge {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (p : ι → ℝ) (w : κ → ℝ) (cover : κ → Finset ι)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    (hw : ∀ j ∈ t, 0 < w j) (hwsum : ∑ j ∈ t, w j ≤ 1)
    (hc : ∀ i ∈ s, p i ≠ 0 → 0 < finiteCoverWeight t w cover i) :
    (∑ i ∈ s, Real.negMulLog (p i)) +
      (∑ i ∈ s, p i * Real.log (finiteCoverWeight t w cover i)) ≤
        (∑ i ∈ s, ∑ j ∈ t, Real.negMulLog (finiteCoverJoint t p w cover i j)) -
          ∑ j ∈ t, Real.negMulLog (finiteCoverLabelWeight s t p w cover j) := by
  have hq : ∀ j ∈ t, 0 ≤ finiteCoverLabelWeight s t p w cover j := by
    intro j hj
    apply Finset.sum_nonneg
    intro i hi
    exact finiteCoverJoint_nonneg t p w cover (hp i hi) (fun k hk ↦ (hw k hk).le) hj
  have hqsum : ∑ j ∈ t, finiteCoverLabelWeight s t p w cover j = 1 := by
    simp only [finiteCoverLabelWeight]
    rw [Finset.sum_comm]
    exact sum_sum_finiteCoverJoint_eq_one s t p w cover hsum hc
  have hbound := finite_entropy_le_cross_entropy t (finiteCoverLabelWeight s t p w cover)
    w hq hqsum hw hwsum
  have he := finiteCover_joint_entropy_eq s t p w cover hc
  linarith

end LpSelfSimilar.Entropy
