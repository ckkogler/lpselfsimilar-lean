module

public import LpSelfSimilar.Probability.ConditionalMoments
public import LpSelfSimilar.Probability.FiniteMixture

@[expose] public section

/-!
The law of total expectation and exact reconstruction of a finite real law from
its conditional laws. Only positive marginal atoms index the mixture, so no
choice of a conditional law on a null event is required.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal

namespace LpSelfSimilar.FiniteProbability

lemma total_expectation {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (g : α → ℝ) :
    expectation p hp g =
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toReal *
      expectation (Entropy.conditionalPMF p f b)
        (Entropy.conditionalPMF_support_finite p hp f b) g) := by
  classical
  let hpf : (p.map f).support.Finite := by simpa using hp.image f
  letI : Fintype (p.map f).support := hpf.fintype
  change expectation p hp g = ∑ b : (p.map f).support, _
  have he (b : (p.map f).support) : ((p.map f) b).toReal *
      expectation (Entropy.conditionalPMF p f b)
        (Entropy.conditionalPMF_support_finite p hp f b) g =
      expectation p hp (fun a ↦ if f a = b then g a else 0) := by
    rw [expectation_conditional]
    exact mul_div_cancel₀ _ (Entropy.marginal_toReal_pos p f b).ne'
  simp_rw [he]
  unfold expectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hfa : f a ∈ (p.map f).support := by
    rw [PMF.support_map]
    exact ⟨a, by simpa using ha, rfl⟩
  rw [Finset.sum_eq_single (⟨f a, hfa⟩ : (p.map f).support)]
  · simp
  · intro b _ hba
    have hb : f a ≠ b := by
      intro h
      apply hba
      exact Subtype.ext h.symm
    simp [hb]
  · simp

lemma conditional_weights_sum {α β : Type*} (p : PMF α) (hp : p.support.Finite) (f : α → β) :
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    ∑ b : (p.map f).support, ((p.map f) b).toNNReal) = 1 := by
  classical
  let hpf : (p.map f).support.Finite := by simpa using hp.image f
  letI : Fintype (p.map f).support := hpf.fintype
  change (∑ b : (p.map f).support, ((p.map f) b).toNNReal) = 1
  apply NNReal.coe_injective
  rw [NNReal.coe_sum, NNReal.coe_one]
  change (∑ b : (p.map f).support, ((p.map f) b).toReal) = 1
  rw [← Finset.sum_subtype hpf.toFinset
    (by simp : ∀ b, b ∈ hpf.toFinset ↔ b ∈ (p.map f).support)
    (fun b ↦ ((p.map f) b).toReal)]
  exact Entropy.sum_support_toReal (p.map f) hpf

/-- An equality of actual measures, not just equality of conditional moments. -/
theorem measure_eq_conditional_mixture {β : Type*} [DecidableEq β]
    (p : PMF ℝ) (hp : p.support.Finite) (f : ℝ → β) :
    p.toMeasure =
    (letI : Fintype (p.map f).support :=
      (show (p.map f).support.Finite from by simpa using hp.image f).fintype
    finiteMixture (fun b : (p.map f).support ↦ ((p.map f) b).toNNReal)
      (fun b ↦ (Entropy.conditionalPMF p f b).toMeasure)) := by
  classical
  let hpf : (p.map f).support.Finite := by simpa using hp.image f
  letI : Fintype (p.map f).support := hpf.fintype
  let w := fun b : (p.map f).support ↦ ((p.map f) b).toNNReal
  let μ := fun b : (p.map f).support ↦ (Entropy.conditionalPMF p f b).toMeasure
  change p.toMeasure = finiteMixture w μ
  have hi (g : ℝ → ℝ) : (∫ x, g x ∂p.toMeasure) = ∫ x, g x ∂finiteMixture w μ := by
    rw [integral_finiteMixture w μ (fun b ↦ integrable_of_finite_support _
      (Entropy.conditionalPMF_support_finite p hp f b) g)]
    rw [← expectation_eq_integral p hp g, total_expectation p hp f g]
    apply Finset.sum_congr rfl
    intro b _
    rw [expectation_eq_integral]
    rfl
  ext E hE
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have h := hi (E.indicator (fun _ ↦ (1 : ℝ)))
  calc
    (p.toMeasure E).toReal = ∫ x, E.indicator (fun _ ↦ (1 : ℝ)) x ∂p.toMeasure :=
      (integral_indicator_one (μ := p.toMeasure) hE).symm
    _ = _ := h
    _ = ((finiteMixture w μ) E).toReal := integral_indicator_one (μ := finiteMixture w μ) hE

end LpSelfSimilar.FiniteProbability
