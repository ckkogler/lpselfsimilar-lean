module

public import LpSelfSimilar.Entropy.FiniteAdditiveChannel

@[expose] public section

/-!
Simultaneously changing signal and noise by an invertible additive coordinate map
preserves information. The map and inverse are measurably specified; in later
applications they are invertible real linear maps on finite Euclidean spaces.
The identity uses exact pushforward laws and does not assume a change-of-variables
formula for differential entropy.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InformationTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

lemma additive_channel_map_equiv {ι E F : Type*} [MeasurableSpace ι]
    [AddGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    [AddGroup F] [MeasurableSpace F] [MeasurableAdd₂ F]
    (X : ι → E) (hX : Measurable X) (ρ : Measure E) [IsProbabilityMeasure ρ]
    (e : E ≃ᵐ F) (hadd : ∀ x y, e (x + y) = e x + e y) :
    (additiveNoiseKernel (ρ.map e)).comap (fun i ↦ e (X i)) (e.measurable.comp hX) =
      ((additiveNoiseKernel ρ).comap X hX).map e := by
  ext i : 1
  rw [Kernel.map_apply _ e.measurable]
  simp only [Kernel.comap_apply, additiveNoiseKernel_apply]
  rw [Measure.map_map (show Measurable (fun y : F ↦ e (X i) + y) by fun_prop) e.measurable,
    Measure.map_map e.measurable (show Measurable (fun y : E ↦ X i + y) by fun_prop)]
  congr 1
  funext x
  exact (hadd (X i) x).symm

/-- Invertible additive coordinate changes preserve finite-signal information. -/
theorem additiveInformation_map_equiv {ι E F : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [AddGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    [AddGroup F] [MeasurableSpace F] [MeasurableAdd₂ F]
    (p : PMF ι) (X : ι → E) (ρ : Measure E) [IsProbabilityMeasure ρ]
    (e : E ≃ᵐ F) (hadd : ∀ x y, e (x + y) = e x + e y) :
    additiveInformation p (fun i ↦ e (X i)) (ρ.map e) = additiveInformation p X ρ := by
  unfold additiveInformation
  rw [additive_channel_map_equiv X (measurable_of_countable X) ρ e hadd,
    finiteInformation_map_measurableEquiv]

end LpSelfSimilar.Entropy
