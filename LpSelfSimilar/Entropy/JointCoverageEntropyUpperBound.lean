module

public import LpSelfSimilar.Entropy.FiniteJointCoverage
public import LpSelfSimilar.Entropy.GraphEntropy
public import LpSelfSimilar.Entropy.FiniteVariationalSupport

@[expose] public section

/-!
# The reverse variational entropy inequality

Given any supported joint law, use its actual label marginal as cover weights.
Coverage-normalized sampling produces a comparison joint law with the same point
marginal. Gibbs' inequality bounds the original conditional entropy by point
entropy minus logarithmic coverage cost. Thus the variational bound applies to
arbitrary finite label families, including repeated supports and null labels.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Every supported finite joint law obeys the reverse logarithmic coverage bound. -/
theorem jointConditionalEntropy_le_entropy_sub_coverageCost {ι κ : Type*}
    [Fintype ι] [Fintype κ] (p : ι → ℝ) (cover : κ → Finset ι)
    {u : ι → κ → ℝ} (hu : u ∈ supportedJointSpace p cover) (hsum : ∑ i, p i = 1) :
    jointConditionalEntropy u ≤ (∑ i, Real.negMulLog (p i)) -
      graphCoverageCost p (finiteCoverWeight Finset.univ (fun j ↦ ∑ i, u i j) cover) := by
  classical
  let q : κ → ℝ := fun j ↦ ∑ i, u i j
  let x := finiteCoverWeight Finset.univ q cover
  let R := finiteCoverJoint Finset.univ p q cover
  have hp : ∀ i, 0 ≤ p i := by
    intro i
    rw [← hu.2.1 i]
    exact Finset.sum_nonneg (fun j _ ↦ hu.1 i j)
  have hq : ∀ j, 0 ≤ q j := fun j ↦ Finset.sum_nonneg (fun i _ ↦ hu.1 i j)
  have hcol (i : ι) (j : κ) : u i j ≤ q j :=
    Finset.single_le_sum (fun k _ ↦ hu.1 k j) (Finset.mem_univ i)
  have hx : ∀ i, p i ≠ 0 → 0 < x i := fun i hi ↦
    (lt_of_le_of_ne (hp i) hi.symm).trans_le (supportedJoint_row_le_label_coverage p cover hu i)
  have hpositive (i : ι) (j : κ) (hij : u i j ≠ 0) :
      0 < p i ∧ 0 < q j ∧ i ∈ cover j := by
    have hpos := lt_of_le_of_ne (hu.1 i j) hij.symm
    refine ⟨hpos.trans_le (supportedJoint_entry_le_row p cover hu i j),
      hpos.trans_le (hcol i j), ?_⟩
    by_contra hi
    exact hij (hu.2.2 i j hi)
  have hR0 (i : ι) (j : κ) : 0 ≤ R i j :=
    finiteCoverJoint_nonneg Finset.univ p q cover (hp i) (fun j _ ↦ hq j) (Finset.mem_univ j)
  have hRpos (i : ι) (j : κ) (hij : u i j ≠ 0) : 0 < R i j := by
    obtain ⟨hpi, hqj, hi⟩ := hpositive i j hij
    change 0 < p i * (if i ∈ cover j then q j else 0) / x i
    rw [ite_eq_left hi]
    exact div_pos (mul_pos hpi hqj) (hx i hpi.ne')
  have hRsum : (∑ ij : ι × κ, R ij.1 ij.2) = 1 := by
    simpa only [Fintype.sum_prod_type] using
      sum_sum_finiteCoverJoint_eq_one Finset.univ Finset.univ p q cover hsum (fun i _ ↦ hx i)
  have hUsum : (∑ ij : ι × κ, u ij.1 ij.2) = 1 := by
    simpa only [Fintype.sum_prod_type, hu.2.1] using hsum
  have hg := finite_entropy_le_cross_entropy_on_support (Finset.univ : Finset (ι × κ))
    (fun ij ↦ u ij.1 ij.2) (fun ij ↦ R ij.1 ij.2) (fun ij _ ↦ hu.1 ij.1 ij.2) hUsum
    (fun ij _ ↦ hR0 ij.1 ij.2) (fun ij _ ↦ hRpos ij.1 ij.2) hRsum.le
  simp only [Fintype.sum_prod_type] at hg
  have hterm (i : ι) (j : κ) :
      u i j * (-Real.log (R i j)) = u i j * (-Real.log (p i)) +
        u i j * (-Real.log (q j)) + u i j * Real.log (x i) := by
    by_cases hij : u i j = 0
    · simp [hij]
    · obtain ⟨hpi, hqj, hi⟩ := hpositive i j hij
      change u i j * (-Real.log (p i * (if i ∈ cover j then q j else 0) / x i)) = _
      rw [ite_eq_left hi, Real.log_div (mul_ne_zero hpi.ne' hqj.ne') (hx i hpi.ne').ne',
        Real.log_mul hpi.ne' hqj.ne']
      ring
  have hrow_weight (b : ι → ℝ) :
      (∑ i, ∑ j, u i j * b i) = ∑ i, p i * b i := by
    simp_rw [← Finset.sum_mul, hu.2.1]
  have hpoint : (∑ i, ∑ j, u i j * (-Real.log (p i))) =
      ∑ i, Real.negMulLog (p i) := by
    rw [hrow_weight]
    simp [Real.negMulLog, mul_neg]
  have hlabel : (∑ i, ∑ j, u i j * (-Real.log (q j))) =
      ∑ j, Real.negMulLog (q j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    change (∑ j, q j * (-Real.log (q j))) = _
    simp [Real.negMulLog, mul_neg]
  have hcost : (∑ i, ∑ j, u i j * Real.log (x i)) = -graphCoverageCost p x := by
    rw [hrow_weight]
    simp [graphCoverageCost, mul_neg]
  simp_rw [hterm] at hg
  simp only [Finset.sum_add_distrib] at hg
  rw [hpoint, hlabel, hcost] at hg
  change (∑ i, ∑ j, Real.negMulLog (u i j)) - (∑ j, Real.negMulLog (q j)) ≤
    (∑ i, Real.negMulLog (p i)) - graphCoverageCost p x
  linarith

end LpSelfSimilar.Entropy
