module

public import LpSelfSimilar.Entropy.ChainRule
public import LpSelfSimilar.Entropy.InjectiveSupport

@[expose] public section

/-!
Conditional entropy of one statistic given another. Joint-law chain rules and
normalized conditional laws identify the expected entropy inside the fibers.
This supplies the comparison between fine and coarse grid entropies.
-/

namespace LpSelfSimilar.Entropy

lemma conditional_pair_map_entropy {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ) (b : (p.map f).support) :
    finiteEntropy ((conditionalPMF p f b).map (fun a ↦ (f a, g a)))
      (by simpa using (conditionalPMF_support_finite p hp f b).image (fun a ↦ (f a, g a))) =
    finiteEntropy ((conditionalPMF p f b).map g)
      (by simpa using (conditionalPMF_support_finite p hp f b).image g) := by
  have he : (conditionalPMF p f b).map (fun a ↦ (f a, g a)) =
      ((conditionalPMF p f b).map g).map (fun c ↦ ((b : β), c)) := by
    rw [PMF.map_comp]
    apply map_congr_on_support
    intro a ha
    rw [conditionalPMF_support] at ha
    exact Prod.ext ha.1 rfl
  apply (finiteEntropy_congr he _ _).trans
  exact finiteEntropy_map_of_injective _ _ (fun _ _ h ↦ (Prod.mk.inj h).2)

lemma averageConditionalEntropy_joint_eq {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ) :
    averageConditionalEntropy (p.map (fun a ↦ (f a, g a)))
      (by simpa using hp.image (fun a ↦ (f a, g a))) Prod.fst =
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      finiteEntropy ((conditionalPMF p f b).map g)
        (by simpa using (conditionalPMF_support_finite p hp f b).image g)) := by
  let q := p.map (fun a ↦ (f a, g a))
  have hfst : q.map Prod.fst = p.map f := by simp [q, PMF.map_comp, Function.comp_def]
  let e : (q.map Prod.fst).support ≃ (p.map f).support :=
    Equiv.setCongr (congrArg PMF.support hfst)
  unfold averageConditionalEntropy
  classical
  letI : Fintype (p.map f).support :=
    (show (p.map f).support.Finite from by simpa using hp.image f).fintype
  letI : Fintype (q.map Prod.fst).support :=
    (show (q.map Prod.fst).support.Finite from by rw [hfst]; simpa using hp.image f).fintype
  apply Fintype.sum_equiv e
    (fun b ↦ ((q.map Prod.fst) b).toReal *
      finiteEntropy (conditionalPMF q Prod.fst b)
        (conditionalPMF_support_finite q (by simpa [q] using hp.image (fun a ↦ (f a, g a))) Prod.fst b))
    (fun b ↦ ((p.map f) b).toReal * finiteEntropy ((conditionalPMF p f b).map g)
      (by simpa using (conditionalPMF_support_finite p hp f b).image g))
  intro b
  have hw : ((q.map Prod.fst) b).toReal = ((p.map f) (e b)).toReal := by
    exact congrArg (fun ν : PMF β ↦ (ν b.val).toReal) hfst
  change ((q.map Prod.fst) b).toReal * _ = _
  rw [hw]
  congr 1
  have hm := map_conditionalPMF p (fun a ↦ (f a, g a)) Prod.fst b
  have he : conditionalPMF q Prod.fst b =
      (conditionalPMF p f (e b)).map (fun a ↦ (f a, g a)) := by
    exact hm.symm
  apply (finiteEntropy_congr he _ _).trans
  exact conditional_pair_map_entropy p hp f g (e b)

/-- Fine entropy minus coarse entropy is bounded by the mean entropy in coarse fibers. -/
theorem entropy_sub_le_conditional_statistic {α β γ : Type*} (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → γ) :
    finiteEntropy (p.map g) (by simpa using hp.image g) -
      finiteEntropy (p.map f) (by simpa using hp.image f) ≤
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      finiteEntropy ((conditionalPMF p f b).map g)
        (by simpa using (conditionalPMF_support_finite p hp f b).image g)) := by
  let q := p.map (fun a ↦ (f a, g a))
  let hq : q.support.Finite := by simpa [q] using hp.image (fun a ↦ (f a, g a))
  have hm := finiteEntropy_map_le q hq Prod.snd
  have hc := finiteEntropy_chain_rule q hq Prod.fst
  rw [conditionalEntropy_eq_average] at hc
  have hfst : q.map Prod.fst = p.map f := by simp [q, PMF.map_comp, Function.comp_def]
  have hsnd : q.map Prod.snd = p.map g := by simp [q, PMF.map_comp, Function.comp_def]
  have hm' := (finiteEntropy_congr hsnd _ (show (p.map g).support.Finite from by
    simpa using hp.image g)).symm.trans_le hm
  have hc' := hc.trans (congrArg (fun z ↦ z + averageConditionalEntropy q hq Prod.fst)
    (finiteEntropy_congr hfst _ (show (p.map f).support.Finite from by simpa using hp.image f)))
  have hav := averageConditionalEntropy_joint_eq p hp f g
  change averageConditionalEntropy q hq Prod.fst = _ at hav
  rw [hav] at hc'
  linarith

end LpSelfSimilar.Entropy
