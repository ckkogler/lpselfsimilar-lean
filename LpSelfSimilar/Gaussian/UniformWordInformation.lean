module

public import LpSelfSimilar.Gaussian.MatrixInformationEquiv
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

/-!
Retaining one coordinate of a uniform finite word in a Gaussian information
difference. Splitting a word at an arbitrary coordinate gives the actual product
of the two uniform laws. The independent-summand inequality then discards the
other coordinates. No injectivity of the sum, or distinctness of digit values,
is required.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Matrix
open scoped MatrixOrder

namespace LpSelfSimilar.Gaussian

private lemma sum_except_add_coordinate {I E : Type*} [Fintype I] [DecidableEq I]
    [AddCommMonoid E] (j : I) (f : I → E) :
    (∑ i : {i : I // i ≠ j}, f i) + f j = ∑ i, f i := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : I ↦ i ≠ j) f
  let : Subsingleton {i : I // ¬i ≠ j} := ⟨fun a b ↦
    Subtype.ext ((not_not.mp a.property).trans (not_not.mp b.property).symm)⟩
  have hs : (∑ i : {i : I // ¬i ≠ j}, f i) = f j := by
    rw [Fintype.sum_subsingleton _ ⟨j, by simp⟩]
  rwa [hs] at h

/-- A single digit's noise-scale information gain is at most the gain for the
whole uniform word sum. Each coordinate may use a different digit function. -/
theorem matrixInformation_difference_uniform_coordinate {I D ι : Type*}
    [Fintype I] [DecidableEq I] [Fintype D] [Nonempty D]
    [MeasurableSpace D] [MeasurableSingletonClass D]
    [Fintype ι] [DecidableEq ι]
    (W : I → D → EuclideanSpace ℝ ι) (j : I)
    (A B : Matrix ι ι ℝ) (hAB : A * Aᴴ ≤ B * Bᴴ) :
    matrixInformation (PMF.uniformOfFintype D) (W j) A -
        matrixInformation (PMF.uniformOfFintype D) (W j) B ≤
      matrixInformation (PMF.uniformOfFintype (I → D)) (fun w ↦ ∑ i, W i (w i)) A -
        matrixInformation (PMF.uniformOfFintype (I → D)) (fun w ↦ ∑ i, W i (w i)) B := by
  classical
  let R := {i : I // i ≠ j} → D
  let e : (R × D) ≃ (I → D) :=
    (Equiv.prodComm R D).trans (Equiv.funSplitAt j D).symm
  let X : R → EuclideanSpace ℝ ι := fun w ↦ ∑ i : {i : I // i ≠ j}, W i (w i)
  let S : (I → D) → EuclideanSpace ℝ ι := fun w ↦ ∑ i, W i (w i)
  have hsum : (fun z : R × D ↦ X z.1 + W j z.2) = fun z ↦ S (e z) := by
    funext z
    have hz := (Equiv.funSplitAt j D).apply_symm_apply (z.2, z.1)
    have hj : e z j = z.2 := congrArg Prod.fst hz
    have hr : (fun i : {i : I // i ≠ j} ↦ e z i) = z.1 := congrArg Prod.snd hz
    change (∑ i : {i : I // i ≠ j}, W i (z.1 i)) + W j z.2 = ∑ i, W i (e z i)
    rw [← hj, ← hr]
    exact sum_except_add_coordinate j (fun i ↦ W i (e z i))
  have h := matrixInformation_difference_add_summand
    (PMF.uniformOfFintype R) (PMF.uniformOfFintype D) X (W j) A B hAB
  rw [pairPMF_uniform, hsum,
    matrixInformation_uniform_reindex e S A, matrixInformation_uniform_reindex e S B] at h
  exact h

end LpSelfSimilar.Gaussian
