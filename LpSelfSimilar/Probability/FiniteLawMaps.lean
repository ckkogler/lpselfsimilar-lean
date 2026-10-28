module

public import LpSelfSimilar.Probability.SupportedJointLaws

@[expose] public section

/-!
# Mapping actual finite and conditional laws

Mapping the atom locations agrees with the pushforward of their real-vector
measure. Scaling fixes the fallback atom zero, so the same identity holds for
all conditional labels, including null columns.
-/

open MeasureTheory
open scoped BigOperators
open LpSelfSimilar.Entropy

namespace LpSelfSimilar.FiniteProbability

/-- Mapping finite atom locations is exactly measure pushforward. -/
theorem realVectorLaw_map {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (z : ι → ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (realVectorLaw p hp hsum z).map f = realVectorLaw p hp hsum (fun i ↦ f (z i)) := by
  unfold realVectorLaw
  rw [PMF.toMeasure_map f ((realVectorPMF p hp hsum).map z) hf,
    PMF.map_comp z (realVectorPMF p hp hsum) f]
  rfl

/-- Scaling a conditional law scales its atom locations, preserving the null-label convention. -/
theorem jointConditionalLaw_map_mul {ι κ : Type*} [Fintype ι]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (z : ι → ℝ) (j : κ) (c : ℝ) :
    (jointConditionalLaw u hu z j).map (fun x ↦ c * x) =
      jointConditionalLaw u hu (fun i ↦ c * z i) j := by
  classical
  by_cases hj : 0 < jointLabelWeight u j
  · simp only [jointConditionalLaw, dif_pos hj]
    exact realVectorLaw_map _ _ _ z (fun x ↦ c * x) (by fun_prop)
  · simp only [jointConditionalLaw, dif_neg hj]
    rw [Measure.map_dirac' (f := fun x : ℝ ↦ c * x) (by fun_prop) 0, mul_zero]

end LpSelfSimilar.FiniteProbability
