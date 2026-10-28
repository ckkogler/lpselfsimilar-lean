module

public import LpSelfSimilar.Probability.RealProbabilityVector
public import LpSelfSimilar.Entropy.Bounds

@[expose] public section

/-!
# Recovering a finitely supported PMF from its actual atoms

The real weights on the support of a finite PMF sum to one. Mapping the resulting
finite real-vector law back to the original atom locations recovers the original
measure, including all collisions already merged in the PMF.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace LpSelfSimilar.FiniteProbability

/-- Real atom weights on the finite support of a PMF have total mass one. -/
theorem sum_real_weights_on_support (p : PMF ℝ) (hp : p.support.Finite) :
    ∑ x : hp.toFinset, (p x).toReal = 1 := by
  change (∑ x ∈ hp.toFinset.attach, (p x.val).toReal) = 1
  rw [Finset.sum_attach hp.toFinset (fun x : ℝ ↦ (p x).toReal)]
  exact Entropy.sum_support_toReal p hp

/-- The real-vector law on the actual finite support is exactly the original PMF measure. -/
theorem realVectorLaw_on_support_eq_toMeasure (p : PMF ℝ) (hp : p.support.Finite) :
    realVectorLaw (fun x : hp.toFinset ↦ (p x).toReal) (fun _ ↦ ENNReal.toReal_nonneg)
      (sum_real_weights_on_support p hp) (fun x ↦ (x : ℝ)) = p.toMeasure := by
  classical
  ext s hs
  have hfinite : p.toMeasure s = ∑ x ∈ hp.toFinset, s.indicator p x := by
    rw [PMF.toMeasure_apply p hs]
    apply tsum_eq_sum
    intro x hx
    have hz : p x = 0 := by
      by_contra h
      exact hx (hp.mem_toFinset.mpr h)
    by_cases hxs : x ∈ s <;> simp [Set.indicator_apply, hxs, hz]
  calc
    _ = ∑ x : hp.toFinset, s.indicator p (x : ℝ) := by
      rw [realVectorLaw_apply _ _ _ _ s hs]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxs : (x : ℝ) ∈ s
      · simp only [Set.indicator_apply, hxs, ite_true,
          ENNReal.ofReal_toReal (p.apply_ne_top _)]
      · simp only [Set.indicator_apply, hxs, ite_false]
    _ = ∑ x ∈ hp.toFinset, s.indicator p x := by
      change (∑ x ∈ hp.toFinset.attach, s.indicator p x.val) = _
      rw [Finset.sum_attach hp.toFinset (s.indicator p)]
    _ = p.toMeasure s := hfinite.symm

end LpSelfSimilar.FiniteProbability
