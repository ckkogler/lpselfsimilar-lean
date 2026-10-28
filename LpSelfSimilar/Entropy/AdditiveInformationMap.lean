module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Entropy.FiniteAdditiveChannel

@[expose] public section

/-!
# Additive information under measurable additive maps

Mapping the actual signal and noise through the same measurable additive map
is channel postprocessing. General finite-channel data processing therefore
bounds its information without an invertibility assumption. A measurable left
inverse gives equality, including singular noise laws and zero input weights.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InformationTheory

namespace LpSelfSimilar.Entropy

lemma additive_channel_map {ι E F : Type*} [MeasurableSpace ι]
    [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    [AddMonoid F] [MeasurableSpace F] [MeasurableAdd₂ F]
    (X : ι → E) (hX : Measurable X) (ρ : Measure E) [IsProbabilityMeasure ρ]
    (f : E → F) (hf : Measurable f) (hadd : ∀ x y, f (x + y) = f x + f y) :
    (additiveNoiseKernel (ρ.map f)).comap (fun i => f (X i)) (hf.comp hX) =
      ((additiveNoiseKernel ρ).comap X hX).map f := by
  ext i : 1
  rw [Kernel.map_apply _ hf]
  simp only [Kernel.comap_apply, additiveNoiseKernel_apply]
  rw [Measure.map_map (show Measurable (fun y : F => f (X i) + y) by fun_prop) hf,
    Measure.map_map hf (show Measurable (fun y : E => X i + y) by fun_prop)]
  congr 1
  funext y
  exact (hadd (X i) y).symm

/-- Simultaneous measurable additive mapping cannot increase actual finite-signal information. -/
theorem additiveInformation_map_le {ι E F : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    [AddMonoid F] [MeasurableSpace F] [MeasurableAdd₂ F]
    (p : PMF ι) (X : ι → E) (ρ : Measure E) [IsProbabilityMeasure ρ]
    (f : E → F) (hf : Measurable f) (hadd : ∀ x y, f (x + y) = f x + f y) :
    additiveInformation p (fun i => f (X i)) (ρ.map f) ≤ additiveInformation p X ρ := by
  let K := (additiveNoiseKernel ρ).comap X (measurable_of_countable X)
  have h := finiteInformation_comp_le p K (Kernel.deterministic f hf)
  rw [Kernel.deterministic_comp_eq_map, ← additive_channel_map X (measurable_of_countable X) ρ f hf hadd] at h
  exact ENNReal.toReal_mono (finiteInformation_ne_top p K) h

/-- A measurable additive left inverse recovers all the information of an embedded channel. -/
theorem additiveInformation_map_eq_of_leftInverse {ι E F : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    [AddMonoid F] [MeasurableSpace F] [MeasurableAdd₂ F]
    (p : PMF ι) (X : ι → E) (ρ : Measure E) [IsProbabilityMeasure ρ]
    (f : E → F) (hf : Measurable f) (hadd : ∀ x y, f (x + y) = f x + f y)
    (g : F → E) (hg : Measurable g) (hgadd : ∀ x y, g (x + y) = g x + g y)
    (hgf : Function.LeftInverse g f) :
    additiveInformation p (fun i => f (X i)) (ρ.map f) = additiveInformation p X ρ := by
  have : IsProbabilityMeasure (ρ.map f) := LpSelfSimilar.Probability.isProbabilityMeasure_map hf.aemeasurable
  apply le_antisymm (additiveInformation_map_le p X ρ f hf hadd)
  have h := additiveInformation_map_le p (fun i => f (X i)) (ρ.map f) g hg hgadd
  have hmap : (ρ.map f).map g = ρ := by
    rw [Measure.map_map hg hf]
    have he : g ∘ f = id := funext hgf
    rw [he, Measure.map_id]
  have hgf' (x : E) : g (f x) = x := hgf x
  simpa only [hmap, hgf'] using h

end LpSelfSimilar.Entropy
