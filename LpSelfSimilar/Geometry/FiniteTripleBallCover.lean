module

public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite greedy ball selection with the exact enlargement factor three

Choose a ball of maximal radius, discard the balls meeting it, and recurse.
Every discarded ball has smaller radius and is contained in the selected
ball with radius multiplied by three. Unlike an approximate maximal-radius
selection for arbitrary infinite families, finiteness retains the exact factor.
-/

open Metric Set

namespace LpSelfSimilar.Geometry

/-- A ball meeting a ball of at least its radius lies in that ball's triple. -/
theorem closedBall_subset_triple_of_not_disjoint {X : Type*} [PseudoMetricSpace X]
    {x y : X} {r s : ℝ} (hrs : r ≤ s)
    (hint : ¬Disjoint (closedBall x r) (closedBall y s)) :
    closedBall x r ⊆ closedBall y (3 * s) := by
  obtain ⟨z, hzx, hzy⟩ := Set.not_disjoint_iff.mp hint
  intro u hu
  have hu' := mem_closedBall.mp hu
  have hzx' := mem_closedBall.mp hzx
  have hzy' := mem_closedBall.mp hzy
  change dist u y ≤ 3 * s
  have h1 := dist_triangle u x z
  have h2 := dist_triangle u z y
  rw [dist_comm x z] at h1
  linarith

/-- A finite family of closed balls has a disjoint subfamily whose triples cover every original ball. -/
theorem finite_disjoint_closedBall_triple_cover {X ι : Type*} [PseudoMetricSpace X]
    (s : Finset ι) (x : ι → X) (r : ι → ℝ) (hr : ∀ i ∈ s, 0 ≤ r i) :
    ∃ t : Finset ι, t ⊆ s ∧
      (t : Set ι).PairwiseDisjoint (fun i => closedBall (x i) (r i)) ∧
      ∀ i ∈ s, ∃ j ∈ t, closedBall (x i) (r i) ⊆ closedBall (x j) (3 * r j) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨p, hp, hmax⟩ := s.exists_max_image r hs
      let v := s.filter (fun i => Disjoint (closedBall (x i) (r i)) (closedBall (x p) (r p)))
      have hvsub : v ⊆ s := Finset.filter_subset _ _
      have hvlt : v ⊂ s := by
        apply Finset.filter_ssubset.mpr
        refine ⟨p, hp, ?_⟩
        intro hdis
        have hmem : x p ∈ closedBall (x p) (r p) := mem_closedBall_self (hr p hp)
        exact Set.disjoint_left.mp hdis hmem hmem
      obtain ⟨t, htv, ht, hcover⟩ := ih v hvlt (fun i hi => hr i (hvsub hi))
      refine ⟨insert p t, ?_, ?_, ?_⟩
      · exact Finset.insert_subset hp (htv.trans hvsub)
      · rw [Finset.coe_insert]
        apply Set.pairwiseDisjoint_insert.mpr
        refine ⟨ht, ?_⟩
        intro j hj hjp
        have hjv := Finset.mem_filter.mp (htv hj)
        exact hjv.2.symm
      · intro i hi
        by_cases hid : Disjoint (closedBall (x i) (r i)) (closedBall (x p) (r p))
        · obtain ⟨j, hj, hc⟩ := hcover i (Finset.mem_filter.mpr ⟨hi, hid⟩)
          exact ⟨j, Finset.mem_insert_of_mem hj, hc⟩
        · exact ⟨p, Finset.mem_insert_self _ _, closedBall_subset_triple_of_not_disjoint
            (hmax i hi) hid⟩
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact ⟨∅, by simp, by simp, by simp⟩

end LpSelfSimilar.Geometry
