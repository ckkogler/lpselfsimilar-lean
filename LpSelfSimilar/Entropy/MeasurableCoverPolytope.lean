module

public import LpSelfSimilar.Entropy.GraphPolytope
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Measurable realizations of independent-set coverages

A random independent set gives a point of the independent-set polytope by its
vertex inclusion probabilities. We prove this for an actual measurable cover:
sets assigned to adjacent vertices are disjoint. The proof integrates their
finite vector of indicators in the compact convex polytope. In particular,
interval lengths realize coverages when the intervals lie in the unit interval.
-/

open Set MeasureTheory

namespace LpSelfSimilar.Entropy

/-- Inclusion probabilities of an actual measurable independent-set cover. -/
theorem measurable_cover_mem_independentSetPolytope {ι Ω : Type*} [Finite ι]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : SimpleGraph ι) (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    (hdis : ∀ i j, G.Adj i j → Disjoint (s i) (s j)) :
    (fun i ↦ μ.real (s i)) ∈ independentSetPolytope G := by
  classical
  let := Fintype.ofFinite ι
  let f : Ω → ι → ℝ := fun t i ↦ (s i).indicator (fun _ ↦ (1 : ℝ)) t
  have hfi : ∀ i, Integrable (fun t ↦ f t i) μ := fun i ↦
    (integrable_const (1 : ℝ)).indicator (hs i)
  have hmem : ∀ t, f t ∈ independentSetPolytope G := by
    intro t
    let a : Finset ι := Finset.univ.filter (fun i ↦ t ∈ s i)
    have ha : G.IsIndepSet (a : Set ι) := by
      intro i hi j hj _ hadj
      exact Set.disjoint_left.mp (hdis i j hadj)
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    have he : f t = vertexSetIndicator a := by
      ext i
      simp [f, a, vertexSetIndicator, Set.indicator]
    rw [he]
    exact vertexSetIndicator_mem_polytope G a ha
  have h := (convex_independentSetPolytope G).integral_mem
    (isCompact_independentSetPolytope G).isClosed (Filter.Eventually.of_forall hmem)
    (Integrable.of_eval hfi)
  have he : (∫ t, f t ∂μ) = fun i ↦ μ.real (s i) := by
    ext i
    rw [eval_integral hfi]
    exact integral_indicator_one (hs i)
  rwa [he] at h

/-- Lengths of independent covering intervals give an actual polytope point. -/
theorem interval_cover_mem_independentSetPolytope {ι : Type*} [Finite ι]
    (G : SimpleGraph ι) (a w : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hw : ∀ i, 0 ≤ w i)
    (hend : ∀ i, a i + w i ≤ 1)
    (hdis : ∀ i j, G.Adj i j → Disjoint (Ico (a i) (a i + w i)) (Ico (a j) (a j + w j))) :
    w ∈ independentSetPolytope G := by
  classical
  let := Fintype.ofFinite ι
  let μ : Measure ℝ := volume.restrict (Ico (0 : ℝ) 1)
  let : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have h := measurable_cover_mem_independentSetPolytope μ G
    (fun i ↦ Ico (a i) (a i + w i)) (fun _ ↦ measurableSet_Ico) hdis
  have he : (fun i ↦ μ.real (Ico (a i) (a i + w i))) = w := by
    ext i
    have hsub : Ico (a i) (a i + w i) ⊆ Ico (0 : ℝ) 1 := by
      intro t ht
      exact ⟨(ha i).trans ht.1, ht.2.trans_le (hend i)⟩
    dsimp [μ]
    rw [measureReal_restrict_apply measurableSet_Ico, inter_eq_left.mpr hsub,
      Real.volume_real_Ico_of_le (by linarith [hw i])]
    ring
  rwa [he] at h

end LpSelfSimilar.Entropy
