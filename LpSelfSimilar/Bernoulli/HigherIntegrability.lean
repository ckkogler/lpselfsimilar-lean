module

public import LpSelfSimilar.Bernoulli.EuclideanSystem
public import LpSelfSimilar.SelfSimilar.HigherIntegrability
public import LpSelfSimilar.Analysis.MeasurePreservingDensity

@[expose] public section

/-!
Theorem 1.1 specialized to the real Bernoulli convolution through an explicit
volume-preserving conjugacy. This qualitative bridge preserves the original
Euclidean theorem and returns a real density with its full measure identity.
-/

open MeasureTheory
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

lemma euclideanLaw_absolutelyContinuous {l : ℝ}
    (hac : convolution l ≪ volume) : euclideanLaw l ≪ volume := by
  have h := realLine.symm.toHomeomorph.measurableEmbedding.absolutelyContinuous_map hac
  change (convolution l).map realLine.symm ≪ volume.map realLine.symm at h
  rwa [realLine_symm_measurePreserving.map_eq] at h

/-- Every absolutely continuous real Bernoulli convolution has an Lp density. -/
theorem higher_integrability_of_absolutelyContinuous {l : ℝ} (hl : 0 < l) (hl1 : l < 1)
    (hac : convolution l ≪ volume) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      ∃ p : ℝ, 1 < p ∧ MemLp f (ENNReal.ofReal p) volume := by
  have hstat : euclideanLaw l = ∑ e : Bool, ENNReal.ofReal (1 / 2 : ℝ) •
      (euclideanLaw l).map (digitSimilarity hl e) := by
    simpa [SelfSimilar.System.IsStationary, selfSimilarSystem] using
      euclideanLaw_stationary hl hl1
  obtain ⟨f, hf0, hf, heq, p, hp, hLp⟩ := self_similar_higher_integrability (by norm_num : 1 ≤ 1)
    (digitSimilarity hl) (fun _ ↦ hl1) (fun _ : Bool ↦ (1 / 2 : ℝ)) (by norm_num)
    (by norm_num [Fintype.sum_bool]) (euclideanLaw l) hstat (euclideanLaw_absolutelyContinuous hac)
  refine ⟨f ∘ realLine.symm, (fun x ↦ hf0 _),
    realLine_symm_measurePreserving.integrable_comp_of_integrable hf, ?_,
    p, hp, hLp.comp_measurePreserving realLine_symm_measurePreserving⟩
  rw [← realLine_map_euclideanLaw l, heq]
  exact map_withDensity_of_measurePreserving realLine.toHomeomorph.toMeasurableEquiv
    realLine_measurePreserving _

end LpSelfSimilar.Bernoulli
