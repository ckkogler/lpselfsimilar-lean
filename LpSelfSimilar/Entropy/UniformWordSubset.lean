module

public import LpSelfSimilar.Entropy.UniformSummand
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

/-!
Retaining any subset of coordinates of a uniform finite word.

If the sum over the selected coordinates is injective as a function of their
digits, then the entropy of the entire sum is at least the logarithm of the
number of selected words. The actual uniform full-word law is split into two
independent uniform laws. This permits arbitrary coordinate subsets and varying
digit functions, and does not require injectivity of the complete word sum.
-/

open MeasureTheory ProbabilityTheory

namespace LpSelfSimilar.Entropy

/-- Exact entropy is unchanged by a uniform reindexing of the underlying finite
sample space, including statistics with collisions. -/
lemma finiteEntropy_uniform_reindex {Ω Ξ E : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype Ξ] [Nonempty Ξ] (e : Ω ≃ Ξ) (S : Ξ → E) :
    finiteEntropy ((PMF.uniformOfFintype Ω).map (fun w ↦ S (e w)))
        (by simpa using (Set.toFinite (PMF.uniformOfFintype Ω).support).image (fun w ↦ S (e w))) =
      finiteEntropy ((PMF.uniformOfFintype Ξ).map S)
        (by simpa using (Set.toFinite (PMF.uniformOfFintype Ξ).support).image S) := by
  have h : (PMF.uniformOfFintype Ω).map (fun w ↦ S (e w)) =
      (PMF.uniformOfFintype Ξ).map S := by
    have he := congrArg (fun q : PMF Ξ ↦ q.map S) (uniformPMF_map_equiv e)
    simpa only [PMF.map_comp, Function.comp_def] using he
  simp only [h]

/-- Entropy of the whole uniform word sum retains the entropy of every subset
whose own sum is injective. -/
theorem entropy_uniform_word_ge_log_card_subset {I D E : Type*}
    [Fintype I] [DecidableEq I] [Fintype D] [Nonempty D]
    [MeasurableSpace D] [MeasurableSingletonClass D]
    [AddCommGroup E] (P : I → Prop) [DecidablePred P]
    (W : I → D → E)
    (hW : Function.Injective (fun w : ({i : I // P i} → D) ↦
      ∑ i : {i : I // P i}, W i (w i))) :
    Real.log (Fintype.card ({i : I // P i} → D)) ≤
      finiteEntropy ((PMF.uniformOfFintype (I → D)).map (fun w ↦ ∑ i, W i (w i)))
        (by
          simpa using (Set.toFinite (PMF.uniformOfFintype (I → D)).support).image
            (fun w ↦ ∑ i, W i (w i))) := by
  classical
  let R := {i : I // ¬P i} → D
  let T := {i : I // P i} → D
  let e : (R × T) ≃ (I → D) :=
    (Equiv.prodComm R T).trans (Equiv.piEquivPiSubtypeProd P (fun _ ↦ D)).symm
  let X : R → E := fun w ↦ ∑ i : {i : I // ¬P i}, W i (w i)
  let Y : T → E := fun w ↦ ∑ i : {i : I // P i}, W i (w i)
  let S : (I → D) → E := fun w ↦ ∑ i, W i (w i)
  have hsum : (fun z : R × T ↦ X z.1 + Y z.2) = fun z ↦ S (e z) := by
    funext z
    have hz := (Equiv.piEquivPiSubtypeProd P (fun _ ↦ D)).apply_symm_apply (z.2, z.1)
    have hT : (fun i : {i : I // P i} ↦ e z i) = z.2 := congrArg Prod.fst hz
    have hR : (fun i : {i : I // ¬P i} ↦ e z i) = z.1 := congrArg Prod.snd hz
    change (∑ i : {i : I // ¬P i}, W i (z.1 i)) +
      (∑ i : {i : I // P i}, W i (z.2 i)) = ∑ i, W i (e z i)
    rw [← hT, ← hR, add_comm]
    exact Fintype.sum_subtype_add_sum_subtype P (fun i ↦ W i (e z i))
  have h := entropy_ge_log_card_uniform_summand (PMF.uniformOfFintype R) X Y hW
  simp only [pairPMF_uniform, hsum, finiteEntropy_uniform_reindex e S] at h
  exact h

end LpSelfSimilar.Entropy
