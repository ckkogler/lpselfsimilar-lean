module

public import LpSelfSimilar.SelfSimilar.Concentration.OpenSetEstimate
public import LpSelfSimilar.SelfSimilar.Concentration.Parameters
public import LpSelfSimilar.Analysis.ExactOpenSetMassRecurrence

@[expose] public section

/-!
# The exact first-concentration mass recurrence

The stopping proof supplies the open-set bound at r = theta*e/K. Absolute
continuity extends it to the actual measurable-set supremum, retaining
D0 = 3/r, beta = 2*e, and the endpoint t = r. This is the written modulus
recurrence accompanying the already proved sharp L2 concentration theorem.
-/

open MeasureTheory Set
open scoped ENNReal
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- The sharp concentration recurrence at its exact constants, for every measurable-set budget. -/
theorem smallSetMass_exact_concentration_recurrence {θ K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 1 ≤ K) (he : 0 < e)
    (hsharp : 12 * K * e < θ) (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hσ : IsStationary hθ σ) (hsupp : σ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hac : σ ≪ volume)
    (hbound : ∀ E : Set ℝ, MeasurableSet E →
      σ E ≤ ENNReal.ofReal K * volume E + ENNReal.ofReal e)
    {t : ℝ} (ht : 0 < t) (htr : t ≤ θ * (e / K)) :
    smallSetMass σ volume (ENNReal.ofReal t) ≤ ENNReal.ofReal (2 * e) *
      smallSetMass σ volume (ENNReal.ofReal ((3 / (θ * (e / K))) * t)) := by
  have hr := concentration_level_mem_Ioo hθ hθ1 hK he hsharp
  apply smallSetMass_exact_recurrence_of_open_sets σ hac
    (div_pos (by norm_num) hr.1) _ ENNReal.ofReal_ne_top _ ht htr
  intro U hU hUv
  exact open_set_mass_le_twice_error_modulus hθ hθ1 (zero_lt_one.trans_le hK)
    he hr.2 σ hσ hsupp hbound hU hUv

end LpSelfSimilar.SelfSimilar.Concentration
