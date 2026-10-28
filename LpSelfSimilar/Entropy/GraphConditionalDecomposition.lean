module

public import LpSelfSimilar.Entropy.GraphCoverRepresentation
public import LpSelfSimilar.Entropy.GraphEntropy
public import LpSelfSimilar.Entropy.FiniteCoverNonnegative

@[expose] public section

/-!
# Conditional probability decompositions from an optimal graph cover

An attained graph-entropy optimizer is represented by actual finite independent
sets and nonnegative cover weights. The coverage-normalized joint construction
then gives the original law as a mixture, with its expected conditional entropy
at least the original entropy minus the graph entropy. Normalization is asserted
for positive-mass labels; null labels contribute zero to every mixture and
entropy sum, and are handled by the proved support form of Gibbs' inequality.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- An actual finite independent-set mixture with the graph-entropy lower bound. -/
theorem exists_graph_conditional_decomposition {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ (κ : Type) (_ : Fintype κ) (q : κ → ℝ) (r : κ → ι → ℝ) (cover : κ → Finset ι),
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j = 1) ∧ (∀ j i, 0 ≤ r j i) ∧
      (∀ j, 0 < q j → ∑ i, r j i = 1) ∧
      (∀ j i, i ∉ cover j → r j i = 0) ∧
      (∀ j, G.IsIndepSet (cover j : Set ι)) ∧
      (∀ i, ∑ j, q j * r j i = p i) ∧
      (∑ i, Real.negMulLog (p i)) - graphEntropy G p ≤
        ∑ j, q j * ∑ i, Real.negMulLog (r j i) := by
  classical
  obtain ⟨x, hx, hx0, hxe, _⟩ := exists_graphEntropy_minimizer G p hp
  obtain ⟨κ, hκ, w, cover, hw, hwsum, hcover, hcov⟩ :=
    exists_finite_cover_of_mem_independentSetPolytope G hx
  let q : κ → ℝ := finiteCoverLabelWeight Finset.univ Finset.univ p w cover
  let r : κ → ι → ℝ := fun j i ↦ finiteCoverJoint Finset.univ p w cover i j / q j
  have hc : ∀ i ∈ Finset.univ, p i ≠ 0 → 0 < finiteCoverWeight Finset.univ w cover i := by
    intro i _ hi
    rw [hcov]
    exact hx0 i hi
  have hjoint : ∀ i j, 0 ≤ finiteCoverJoint Finset.univ p w cover i j := fun i j ↦
    finiteCoverJoint_nonneg Finset.univ p w cover (hp i) (fun j _ ↦ hw j) (Finset.mem_univ j)
  have hq : ∀ j, 0 ≤ q j := fun j ↦ Finset.sum_nonneg (fun i _ ↦ hjoint i j)
  have hqsum : ∑ j, q j = 1 := by
    simp only [q, finiteCoverLabelWeight]
    rw [Finset.sum_comm]
    exact sum_sum_finiteCoverJoint_eq_one Finset.univ Finset.univ p w cover hsum hc
  refine ⟨κ, hκ, q, r, cover, hq, hqsum, (fun j i ↦ div_nonneg (hjoint i j) (hq j)),
    ?_, ?_, hcover, ?_, ?_⟩
  · intro j hj
    exact sum_finiteCover_conditional_eq_one Finset.univ Finset.univ p w cover j hj
  · intro j i hi
    exact finiteCover_conditional_eq_zero_of_not_mem Finset.univ Finset.univ p w cover hi
  · intro i
    exact finiteCover_mixture_eq Finset.univ Finset.univ p w cover (fun i _ ↦ hp i)
      (fun j _ ↦ hw j) hc (Finset.mem_univ i)
  · have h := finiteCover_expected_entropy_ge_of_nonneg Finset.univ Finset.univ p w cover
      (fun i _ ↦ hp i) hsum (fun j _ ↦ hw j) hwsum.le hc
    have hlog : (∑ i, p i * Real.log (finiteCoverWeight Finset.univ w cover i)) =
        -graphEntropy G p := by
      rw [hcov, ← hxe]
      simp [graphCoverageCost, mul_neg]
    rw [hlog] at h
    exact h

end LpSelfSimilar.Entropy
