module

public import LpSelfSimilar.Entropy.MeasurableGraphChoices
public import LpSelfSimilar.Entropy.SupportedJointConditionals

@[expose] public section

/-!
# Measurable maximizing joint laws for the sixteen-scale band

Choose a maximizing joint law once for each finite graph. Composing with the
band graph gives a measurable joint array at every real scale. At positive
scales its canonical allowed supports have at most sixteen vertices. Column
marginals and normalized conditional vectors are measurable as well.
-/

open Set

namespace LpSelfSimilar.Entropy

/-- Every canonical support for the band-complement graph has at most sixteen points. -/
theorem bandIndependentCover_card_le_sixteen {ι : Type*}
    (z : ι → ℝ) (a : ℝ) (ha : 0 < a) (s : Finset ι) :
    (graphIndependentCover (distanceBandGraph z a (16 * a))ᶜ s).card ≤ 16 := by
  apply distanceBandGraph_clique_card_le_sixteen z a ha
  intro i hi j hj hij
  have hn := graphIndependentCover_isIndepSet (distanceBandGraph z a (16 * a))ᶜ s hi hj hij
  by_contra he
  exact hn ⟨hij, he⟩

/-- An attained maximizing joint law varying measurably over every scale. -/
theorem exists_measurable_distanceBand_maximizer {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ∃ u : ℝ → ι → Finset ι → ℝ, Measurable u ∧
      (∀ a, u a ∈ supportedJointSpace p
        (graphIndependentCover (distanceBandGraph z a (16 * a))ᶜ)) ∧
      (∀ a, jointConditionalEntropy (u a) / Real.log 2 =
        distanceBandConditionalEntropyBits z a p) := by
  classical
  choose u hu he using fun G : SimpleGraph ι ↦
    exists_graphConditionalEntropy_maximizer G p hp
  refine ⟨fun a ↦ u (distanceBandGraph z a (16 * a))ᶜ,
    measurable_function_of_distanceBandGraph z (fun G ↦ u Gᶜ), fun a ↦ hu _, ?_⟩
  intro a
  simp only [(he (distanceBandGraph z a (16 * a))ᶜ).1,
    distanceBandConditionalEntropyBits, graphConditionalEntropyBits]

/-- Column marginals of a measurable family of finite joint laws are measurable. -/
theorem measurable_jointLabelWeight {ι κ Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {u : Ω → ι → κ → ℝ} (hu : Measurable u) :
    Measurable (fun x j ↦ jointLabelWeight (u x) j) := by
  unfold jointLabelWeight
  fun_prop

/-- Normalization by column mass is measurable, including the zero column convention. -/
theorem measurable_jointConditionalWeight {ι κ Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] {u : Ω → ι → κ → ℝ} (hu : Measurable u) :
    Measurable (fun x j i ↦ jointConditionalWeight (u x) j i) := by
  unfold jointConditionalWeight jointLabelWeight
  fun_prop

end LpSelfSimilar.Entropy
