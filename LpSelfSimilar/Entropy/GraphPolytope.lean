module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

/-!
# The finite independent-set polytope

The polytope consists of convex combinations of ordinary zero-one indicators of
independent vertex sets. Its coordinates are cover probabilities. Compactness
and an explicit positive point allow logarithmic entropy to be minimized without
assigning an artificial finite cost to an uncovered vertex of positive mass.
-/

open Set
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- The real indicator vector of a finite vertex set. -/
noncomputable def vertexSetIndicator {ι : Type*} (s : Finset ι) : ι → ℝ := by
  classical
  exact fun i ↦ if i ∈ s then 1 else 0

/-- Convex combinations of independent-set indicators of a graph. -/
noncomputable def independentSetPolytope {ι : Type*} (G : SimpleGraph ι) : Set (ι → ℝ) :=
  convexHull ℝ (Set.range fun s : {s : Finset ι // G.IsIndepSet (s : Set ι)} ↦
    vertexSetIndicator s.val)

theorem convex_independentSetPolytope {ι : Type*} (G : SimpleGraph ι) :
    Convex ℝ (independentSetPolytope G) :=
  convex_convexHull ℝ _

theorem isCompact_independentSetPolytope {ι : Type*} [Finite ι] (G : SimpleGraph ι) :
    IsCompact (independentSetPolytope G) := by
  classical
  let := Fintype.ofFinite ι
  exact (Set.finite_range _).isCompact_convexHull ℝ

theorem vertexSetIndicator_mem_polytope {ι : Type*} (G : SimpleGraph ι)
    (s : Finset ι) (hs : G.IsIndepSet (s : Set ι)) :
    vertexSetIndicator s ∈ independentSetPolytope G :=
  subset_convexHull ℝ _ ⟨⟨s, hs⟩, rfl⟩

/-- Every cover probability belongs to the ordinary unit interval. -/
theorem independentSetPolytope_coordinate_bounds {ι : Type*} (G : SimpleGraph ι)
    {x : ι → ℝ} (hx : x ∈ independentSetPolytope G) (i : ι) :
    0 ≤ x i ∧ x i ≤ 1 := by
  classical
  have hsub : independentSetPolytope G ⊆ Set.pi Set.univ (fun _ : ι ↦ Icc (0 : ℝ) 1) := by
    apply convexHull_min
    · rintro _ ⟨s, rfl⟩ i _
      simp only [vertexSetIndicator, mem_Icc]
      split_ifs <;> norm_num
    · exact convex_pi (fun _ _ ↦ convex_Icc (0 : ℝ) 1)
  exact hsub hx i (Set.mem_univ i)

/-- Averaging singleton independent sets gives uniform positive coverage. -/
theorem uniform_mem_independentSetPolytope {ι : Type*} [Fintype ι] [Nonempty ι]
    (G : SimpleGraph ι) :
    (fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹) ∈ independentSetPolytope G := by
  classical
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply mem_convexHull_of_exists_fintype
    (fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹) (fun i ↦ vertexSetIndicator {i})
  · intro i
    exact inv_nonneg.mpr hc.le
  · simp [hc.ne']
  · intro i
    refine ⟨⟨{i}, ?_⟩, rfl⟩
    simp [SimpleGraph.isIndepSet_iff]
  · ext i
    simp [vertexSetIndicator, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

end LpSelfSimilar.Entropy
