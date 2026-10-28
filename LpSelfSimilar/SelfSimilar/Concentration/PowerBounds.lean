module

public import LpSelfSimilar.SelfSimilar.Concentration.ExactModulus
public import LpSelfSimilar.SelfSimilar.Concentration.PowerParameters
public import LpSelfSimilar.Analysis.SmallSetMassPowers
public import LpSelfSimilar.Analysis.DensityPowerTails

@[expose] public section

/-!
# The concentration modulus and density power bounds

The constants in these estimates are selected once, before the volume budget
or density level. Their exponents are exactly the logarithmic exponent from
the stopped cover and -1/(1-alpha) for density superlevels. Absolute continuity
in the density formulation follows from its explicit measure representation.
-/

open MeasureTheory Set
open scoped ENNReal
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- The exact concentration recurrence gives the written small-set power estimate. -/
theorem concentration_mass_power_bound {θ K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 1 ≤ K) (he : 0 < e)
    (hsharp : 12 * K * e < θ) (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hσ : IsStationary hθ σ) (hsupp : σ (Icc (0 : ℝ) 1)ᶜ = 0) (hac : σ ≪ volume)
    (hbound : ∀ E : Set ℝ, MeasurableSet E →
      σ E ≤ ENNReal.ofReal K * volume E + ENNReal.ofReal e) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      smallSetMass σ volume (ENNReal.ofReal t) ≤
        ENNReal.ofReal (C * t ^ massDecayExponent (2 * e) (3 / (θ * (e / K)))) := by
  obtain ⟨hD, hβ, hβ1, _⟩ := concentration_power_parameters hθ hθ1 hK he hsharp
  have hr := concentration_level_mem_Ioo hθ hθ1 hK he hsharp
  apply smallSetMass_le_rpow_of_recurrence σ volume hr.1 hD hβ hβ1
  intro t ht htr
  exact smallSetMass_exact_concentration_recurrence hθ hθ1 hK he hsharp σ hσ hsupp
    hac hbound ht htr.le

/-- The source's two power estimates, with one constant independent of volume and density levels. -/
theorem concentration_mass_and_density_power_bounds {θ K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 1 ≤ K) (he : 0 < e)
    (hsharp : 12 * K * e < θ) (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hσ : IsStationary hθ σ) (hsupp : σ (Icc (0 : ℝ) 1)ᶜ = 0)
    {f : ℝ → ℝ} (hf : Measurable f)
    (hdensity : σ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hbound : ∀ E : Set ℝ, MeasurableSet E →
      σ E ≤ ENNReal.ofReal K * volume E + ENNReal.ofReal e) :
    let α := massDecayExponent (2 * e) (3 / (θ * (e / K)))
    ∃ C : ℝ, 0 < C ∧
      (∀ t : ℝ, 0 < t → smallSetMass σ volume (ENNReal.ofReal t) ≤ ENNReal.ofReal (C * t ^ α)) ∧
      (∀ u : ℝ, 0 < u → (volume {x | u < f x}).toReal ≤
        C ^ (1 / (1 - α)) * u ^ (-1 / (1 - α))) := by
  have hac : σ ≪ volume := by
    rw [hdensity]
    exact withDensity_absolutelyContinuous volume _
  obtain ⟨C, hC, hmass⟩ := concentration_mass_power_bound hθ hθ1 hK he hsharp σ hσ hsupp hac hbound
  have hα := (concentration_power_parameters hθ hθ1 hK he hsharp).2.2.2
  exact ⟨C, hC, hmass, fun _ hu => density_superlevel_volume_rpow_bound volume σ hf hdensity
    hC hα.2 hmass hu⟩

end LpSelfSimilar.SelfSimilar.Concentration
