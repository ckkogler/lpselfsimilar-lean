module

public import LpSelfSimilar.SelfSimilar.Concentration.OpenSetEstimate
public import LpSelfSimilar.SelfSimilar.Concentration.Parameters
public import LpSelfSimilar.Analysis.OpenSetMassRecurrence
public import LpSelfSimilar.Analysis.DensityL2FromSmallSetMass

@[expose] public section

/-!
# Sharp L2 upgrade by first-concentration stopping

This is the normalized stationary-measure form of Lemma 6.1. A probability
density supported on [0,1], stationary for theta*x and theta*x+1-theta, belongs
to L2 whenever its coarse small-set bound has constants K>=1, e>0 and
12*K*e<theta. All stopping, covering, limiting and constant-selection inputs
are proved in the preceding modules. No separation assumption is imposed.
-/

open MeasureTheory Set
open scoped ENNReal
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- Lemma 6.1: the exact strict condition 12*K*e<theta upgrades the normalized density to L2. -/
theorem memLp_two_of_small_set_bound {θ K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 1 ≤ K) (he : 0 < e)
    (hsharp : 12 * K * e < θ) (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hσ : IsStationary hθ σ) (hsupp : σ (Icc (0 : ℝ) 1)ᶜ = 0)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hdensity : σ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hbound : ∀ E : Set ℝ, MeasurableSet E →
      σ E ≤ ENNReal.ofReal K * volume E + ENNReal.ofReal e) :
    MemLp f 2 volume := by
  let r := θ * (e / K)
  let β := 2 * e
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hr : r ∈ Ioo 0 1 := concentration_level_mem_Ioo hθ hθ1 hK he hsharp
  have hβ : 0 < β := by dsimp only [β]; positivity
  obtain ⟨D, hD₀, hD, hβD, hratio⟩ :=
    exists_enlarged_concentration_multiplier hθ hθ1 hK he hsharp
  have hopen (U : Set ℝ) (hU : IsOpen U) (hv : volume U ≤ ENNReal.ofReal r) :
      σ U ≤ ENNReal.ofReal β * smallSetMass σ volume (ENNReal.ofReal (3 / r) * volume U) :=
    open_set_mass_le_twice_error_modulus hθ hθ1 hK0 he hr.2 σ hσ hsupp hbound hU hv
  have hrec (t : ℝ) (ht : 0 < t) (htr : t < r) :
      smallSetMass σ volume (ENNReal.ofReal t) ≤
        ENNReal.ofReal β * smallSetMass σ volume (ENNReal.ofReal (D * t)) :=
    smallSetMass_recurrence_of_open_sets σ (div_pos (by norm_num) hr.1) hD₀ _ hopen ht htr
  have hR : 0 < r / 2 := by positivity
  have hRr : r / 2 < r := by linarith [hr.1]
  have hmass (n : ℕ) : smallSetMass σ volume (ENNReal.ofReal ((r / 2) / D ^ n)) ≤
      ENNReal.ofReal β ^ n :=
    smallSetMass_le_geometric_of_recurrence σ volume hR hRr hD _ hrec n
  exact memLp_two_of_geometric_smallSetMass volume σ hf hf0 hdensity hR
    (zero_lt_one.trans hD) hβ hβD hratio hmass

end LpSelfSimilar.SelfSimilar.Concentration
