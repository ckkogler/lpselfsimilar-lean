module

public import Mathlib.Order.Preorder.Chain
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic

@[expose] public section

/-!
# Intervals from weights on a finite partially ordered set

For each vertex, take the largest total weight of a chain strictly preceding it.
The interval starting at that value and of length equal to the vertex weight
comes before the interval of every strictly later vertex. If all chain weights
are at most one, every such interval ends before one. This is the finite
weighted chain/antichain construction used to realize complementary coverages.
-/

open Set
open scoped BigOperators

namespace LpSelfSimilar.Combinatorics

/-- All finite chains whose vertices strictly precede the given vertex. -/
noncomputable def predecessorChains {ι : Type*} [Fintype ι] [PartialOrder ι]
    (i : ι) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (fun s ↦ IsChain (· ≤ ·) (s : Set ι) ∧ ∀ j ∈ s, j < i)

lemma empty_mem_predecessorChains {ι : Type*} [Fintype ι] [PartialOrder ι] (i : ι) :
    ∅ ∈ predecessorChains i := by
  classical
  simp [predecessorChains]

/-- The largest total weight of a chain strictly preceding a vertex. -/
noncomputable def predecessorChainWeight {ι : Type*} [Fintype ι] [PartialOrder ι]
    (w : ι → ℝ) (i : ι) : ℝ :=
  (predecessorChains i).sup' ⟨∅, empty_mem_predecessorChains i⟩ (fun s ↦ ∑ j ∈ s, w j)

/-- An actual maximizing predecessor chain exists in the finite family. -/
theorem exists_predecessorChainWeight_maximizer {ι : Type*} [Fintype ι] [PartialOrder ι]
    (w : ι → ℝ) (i : ι) :
    ∃ s : Finset ι, IsChain (· ≤ ·) (s : Set ι) ∧ (∀ j ∈ s, j < i) ∧
      predecessorChainWeight w i = ∑ j ∈ s, w j := by
  classical
  obtain ⟨s, hs, he⟩ := Finset.exists_mem_eq_sup'
    (s := predecessorChains i) ⟨∅, empty_mem_predecessorChains i⟩ (fun s ↦ ∑ j ∈ s, w j)
  simp only [predecessorChains, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  exact ⟨s, hs.1, hs.2, he⟩

/-- The empty predecessor chain guarantees a nonnegative starting point. -/
theorem predecessorChainWeight_nonneg {ι : Type*} [Fintype ι] [PartialOrder ι]
    (w : ι → ℝ) (i : ι) : 0 ≤ predecessorChainWeight w i := by
  simpa [predecessorChainWeight] using
    (Finset.le_sup' (fun s : Finset ι ↦ ∑ j ∈ s, w j) (empty_mem_predecessorChains i))

/-- Comparable vertices have ordered, nonoverlapping half-open intervals. -/
theorem predecessorChainWeight_add_le {ι : Type*} [Fintype ι] [PartialOrder ι]
    (w : ι → ℝ) {i j : ι} (hij : i < j) :
    predecessorChainWeight w i + w i ≤ predecessorChainWeight w j := by
  classical
  obtain ⟨s, hs, hsi, he⟩ := exists_predecessorChainWeight_maximizer w i
  have hi : i ∉ s := fun hi ↦ (lt_irrefl i) (hsi i hi)
  have hchain : IsChain (· ≤ ·) ((insert i s : Finset ι) : Set ι) := by
    rw [Finset.coe_insert]
    exact hs.insert (fun k hk _ ↦ Or.inr (hsi k hk).le)
  have hm : insert i s ∈ predecessorChains j := by
    simp only [predecessorChains, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hchain, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hij
    · exact (hsi k hk).trans hij
  have h := Finset.le_sup' (fun s : Finset ι ↦ ∑ k ∈ s, w k) hm
  change (∑ k ∈ insert i s, w k) ≤ predecessorChainWeight w j at h
  simpa only [Finset.sum_insert hi, he, add_comm] using h

/-- A unit bound on every chain places all interval endpoints at most one. -/
theorem predecessorChainWeight_add_le_one {ι : Type*} [Fintype ι] [PartialOrder ι]
    (w : ι → ℝ) (hchain : ∀ s : Finset ι, IsChain (· ≤ ·) (s : Set ι) →
      (∑ j ∈ s, w j) ≤ 1) (i : ι) :
    predecessorChainWeight w i + w i ≤ 1 := by
  classical
  obtain ⟨s, hs, hsi, he⟩ := exists_predecessorChainWeight_maximizer w i
  have hi : i ∉ s := fun hi ↦ (lt_irrefl i) (hsi i hi)
  have hc : IsChain (· ≤ ·) ((insert i s : Finset ι) : Set ι) := by
    rw [Finset.coe_insert]
    exact hs.insert (fun k hk _ ↦ Or.inr (hsi k hk).le)
  simpa [Finset.sum_insert hi, he, add_comm] using hchain (insert i s) hc

end LpSelfSimilar.Combinatorics
