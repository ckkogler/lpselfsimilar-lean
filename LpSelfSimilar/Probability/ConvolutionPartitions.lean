module

public import LpSelfSimilar.Probability.FinsetConvolution

@[expose] public section

/-!
Regrouping finitely many probability laws along disjoint finite partitions.
These identities justify collecting individual Bernoulli digits into blocks
and retaining every unused digit as a separate convolution factor.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar

lemma finsetConvolution_union {I : Type*} [DecidableEq I] (s t : Finset I)
    (μ : I → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (hd : Disjoint s t) :
    finsetConvolution (s ∪ t) μ = finsetConvolution s μ ∗ finsetConvolution t μ := by
  rw [finsetConvolution_split (s ∪ t) s μ Finset.subset_union_left,
    Finset.union_sdiff_cancel_left hd]

lemma finsetConvolution_congr {I : Type*} (s : Finset I) (μ ν : I → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (h : ∀ i ∈ s, μ i = ν i) : finsetConvolution s μ = finsetConvolution s ν := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro h
    rw [finsetConvolution_insert s μ hi, finsetConvolution_insert s ν hi,
      h i (Finset.mem_insert_self _ _), ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))]

lemma finsetConvolution_image {I J : Type*} [DecidableEq J] (s : Finset I)
    (g : I → J) (hg : Function.Injective g) (μ : J → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] :
    finsetConvolution (s.image g) μ = finsetConvolution s (fun i ↦ μ (g i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hgi : g i ∉ s.image g := by
      intro h
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp h
      exact hi ((hg he) ▸ hj)
    rw [Finset.image_insert, finsetConvolution_insert _ μ hgi,
      finsetConvolution_insert _ _ hi, ih]

lemma finsetConvolution_biUnion {I J : Type*} [DecidableEq I] [DecidableEq J]
    (s : Finset I) (A : I → Finset J) (μ : J → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)]
    (hA : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) :
    finsetConvolution (s.biUnion A) μ =
      finsetConvolution s (fun i ↦ finsetConvolution (A i) μ) := by
  revert hA
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro hA
    have hsmall : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (A j) (A k) :=
      fun j hj k hk hne ↦ hA j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hne
    have hd : Disjoint (A i) (s.biUnion A) := by
      apply (Finset.disjoint_biUnion_right _ _ _).mpr
      intro j hj
      exact hA i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (by intro he; subst j; exact hi hj)
    rw [Finset.biUnion_insert, finsetConvolution_union _ _ μ hd,
      finsetConvolution_insert _ _ hi, ih hsmall]

end LpSelfSimilar
