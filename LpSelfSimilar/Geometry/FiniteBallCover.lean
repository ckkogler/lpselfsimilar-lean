module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.Tactic

@[expose] public section

/-! Finite disjoint-ball selection with enlargement factor four. -/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

/-- A finite version of Mathlib's Vitali selection with enlargement factor four. -/
lemma finite_disjoint_ball_cover {X ι : Type*} [PseudoMetricSpace X]
    (s : Finset ι) (x : ι → X) (r : ι → ℝ) :
    ∃ t : Finset ι, t ⊆ s ∧
      (t : Set ι).PairwiseDisjoint (fun i ↦ ball (x i) (r i)) ∧
      ∀ i ∈ s, ∃ j ∈ t, ball (x i) (r i) ⊆ ball (x j) (4 * r j) := by
  classical
  obtain ⟨R, hR⟩ := (s.finite_toSet.image r).bddAbove
  obtain ⟨u, hus, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball (s : Set ι) x r R
      (fun i hi ↦ hR (mem_image_of_mem r hi)) 4 (by norm_num)
  have huf : u.Finite := s.finite_toSet.subset hus
  refine ⟨huf.toFinset, ?_, ?_, ?_⟩
  · simpa using hus
  · simpa using hdisj
  · intro i hi
    obtain ⟨j, hj, hij⟩ := hcover i hi
    exact ⟨j, by simpa using hj, hij⟩

end LpSelfSimilar
