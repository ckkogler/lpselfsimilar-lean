module

public import LpSelfSimilar.SelfSimilar.Concentration.PowerBounds
public import LpSelfSimilar.Analysis.DensityPowerMoments

@[expose] public section

/-!
# Sharp L2 concentration via the written logarithmic power argument

This gives the full normalized concentration lemma through its explicit
power-tail and layer-cake route. It complements the preserved geometric-moment
proof: no analytic input or compact-support assumption is added to that lemma.
-/

open MeasureTheory Set
open scoped ENNReal
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- The full sharp concentration lemma, now through the source's power and layer-cake argument. -/
theorem memLp_two_of_small_set_bound_via_layercake {θ K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 1 ≤ K) (he : 0 < e)
    (hsharp : 12 * K * e < θ) (σ : Measure ℝ) [IsProbabilityMeasure σ]
    (hσ : IsStationary hθ σ) (hsupp : σ (Icc (0 : ℝ) 1)ᶜ = 0)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hdensity : σ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hbound : ∀ E : Set ℝ, MeasurableSet E →
      σ E ≤ ENNReal.ofReal K * volume E + ENNReal.ofReal e) :
    MemLp f 2 volume := by
  let α := massDecayExponent (2 * e) (3 / (θ * (e / K)))
  obtain ⟨C, hC, _, htail⟩ := concentration_mass_and_density_power_bounds hθ hθ1 hK he
    hsharp σ hσ hsupp hf hdensity hbound
  have hα : α ∈ Ioo (1 / 2) 1 :=
    (concentration_power_parameters hθ hθ1 hK he hsharp).2.2.2
  have hκ : 2 < 1 / (1 - α) := by
    apply (lt_div_iff₀ (sub_pos.mpr hα.2)).mpr
    linarith [hα.1]
  apply memLp_two_of_density_power_tail volume σ hf hf0 hdensity
    (C := C ^ (1 / (1 - α))) (κ := 1 / (1 - α)) (by positivity) hκ
  intro u hu
  simpa only [neg_div] using htail u hu

end LpSelfSimilar.SelfSimilar.Concentration
