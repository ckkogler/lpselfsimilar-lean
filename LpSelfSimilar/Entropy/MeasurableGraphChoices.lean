module

public import LpSelfSimilar.Entropy.GraphMonotonicity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

@[expose] public section

/-!
# Measurable choices for finite graph families

A graph on a fixed finite vertex set has only finitely many possible values.
Measurability of its edge predicates therefore makes every graph-dependent
choice measurable. In particular, choosing an attained entropy maximizer once
for each graph gives measurable maximizing joint laws as a distance scale varies.
No measurable selection theorem or regularity of the maximizer is assumed.
-/

open Set

namespace LpSelfSimilar.Entropy

/-- Every function of a finite graph family with measurable edges is measurable. -/
theorem measurable_function_of_finite_graph {ι Ω E : Type*} [Finite ι]
    [MeasurableSpace Ω] [MeasurableSpace E] (g : Ω → SimpleGraph ι)
    (hg : ∀ i j, MeasurableSet {x | (g x).Adj i j}) (F : SimpleGraph ι → E) :
    Measurable (fun x ↦ F (g x)) := by
  classical
  let : MeasurableSpace (SimpleGraph ι) := ⊤
  have hmeas : Measurable g := by
    apply measurable_to_countable' (f := g)
    intro G
    have he : g ⁻¹' {G} = ⋂ i, ⋂ j, {x | (g x).Adj i j ↔ G.Adj i j} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_ofPred_eq]
      constructor
      · intro h i j
        rw [h]
      · intro h
        ext i j
        exact h i j
    rw [he]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hG : G.Adj i j
    · simpa only [hG, iff_true] using hg i j
    · convert (hg i j).compl using 1
      ext x
      simp only [mem_ofPred_eq, hG, iff_false, mem_compl_iff]
  exact measurable_from_top.comp hmeas

/-- Arbitrary graph-dependent quantities are measurable for a varying near radius. -/
theorem measurable_function_of_nearDistanceGraph {ι E : Type*} [Finite ι]
    [MeasurableSpace E] (z : ι → ℝ) (F : SimpleGraph ι → E) :
    Measurable (fun a : ℝ ↦ F (nearDistanceGraph z a)) := by
  apply measurable_function_of_finite_graph
  intro i j
  by_cases hij : i = j
  · simp [nearDistanceGraph, hij]
  · simpa [nearDistanceGraph, hij] using
      (measurableSet_lt measurable_const measurable_id :
        MeasurableSet {a : ℝ | |z i - z j| < a})

/-- Arbitrary graph-dependent quantities are measurable for the exact band `[a,16a)`. -/
theorem measurable_function_of_distanceBandGraph {ι E : Type*} [Finite ι]
    [MeasurableSpace E] (z : ι → ℝ) (F : SimpleGraph ι → E) :
    Measurable (fun a : ℝ ↦ F (distanceBandGraph z a (16 * a))) := by
  apply measurable_function_of_finite_graph
  intro i j
  by_cases hij : i = j
  · simp [distanceBandGraph, hij]
  · have hl : MeasurableSet {a : ℝ | a ≤ |z i - z j|} :=
      measurableSet_le measurable_id measurable_const
    have hu : MeasurableSet {a : ℝ | |z i - z j| < 16 * a} :=
      measurableSet_lt measurable_const (measurable_const.mul measurable_id)
    simpa [distanceBandGraph, hij, ofPred_and] using hl.inter hu

/-- The actual maximum conditional entropy of the sixteen-scale band is measurable. -/
theorem measurable_distanceBandConditionalEntropyBits {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (p : ι → ℝ) : Measurable (fun a : ℝ ↦
      distanceBandConditionalEntropyBits z a p) :=
  measurable_function_of_distanceBandGraph z (fun G ↦ graphConditionalEntropyBits Gᶜ p)

/-- Choose an attained maximizing joint law measurably for any finite graph family. -/
theorem exists_measurable_graphConditionalEntropy_maximizer {ι Ω : Type*} [Fintype ι]
    [MeasurableSpace Ω] (g : Ω → SimpleGraph ι)
    (hg : ∀ i j, MeasurableSet {x | (g x).Adj i j})
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    ∃ u : Ω → ι → Finset ι → ℝ, Measurable u ∧
      (∀ x, u x ∈ supportedJointSpace p (graphIndependentCover (g x))) ∧
      (∀ x, jointConditionalEntropy (u x) = graphConditionalEntropy (g x) p) := by
  classical
  choose u hu he using fun G : SimpleGraph ι ↦
    exists_graphConditionalEntropy_maximizer G p hp
  exact ⟨fun x ↦ u (g x), measurable_function_of_finite_graph g hg u,
    fun x ↦ hu (g x), fun x ↦ (he (g x)).1⟩

end LpSelfSimilar.Entropy
