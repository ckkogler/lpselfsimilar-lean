module

public import LpSelfSimilar.Entropy.GraphPolytope
public import LpSelfSimilar.Entropy.FiniteCover

@[expose] public section

/-!
# Finite weighted covers represented by the independent-set polytope

An actual polytope point has a finite convex-combination presentation. Selecting
the independent set behind each generator makes that presentation exactly the
coverage sum used by the finite conditional-law construction.
-/

open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Every independent-set polytope point is an actual finite nonnegative cover. -/
theorem exists_finite_cover_of_mem_independentSetPolytope {ι : Type*}
    (G : SimpleGraph ι) {x : ι → ℝ} (hx : x ∈ independentSetPolytope G) :
    ∃ (κ : Type) (_ : Fintype κ) (w : κ → ℝ) (cover : κ → Finset ι),
      (∀ j, 0 ≤ w j) ∧ (∑ j, w j = 1) ∧
      (∀ j, G.IsIndepSet (cover j : Set ι)) ∧
      finiteCoverWeight Finset.univ w cover = x := by
  classical
  obtain ⟨κ, hκ, w, z, hw, hsum, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp hx
  choose c hc using hz
  refine ⟨κ, hκ, w, (fun j ↦ (c j).val), hw, hsum, (fun j ↦ (c j).property), ?_⟩
  ext i
  simp_rw [← hc] at he
  simpa [finiteCoverWeight, vertexSetIndicator, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_ite] using congrFun he i

end LpSelfSimilar.Entropy
