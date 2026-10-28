module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Entropy.AdditiveInformationMap
public import Mathlib.MeasureTheory.Group.Convolution

@[expose] public section

/-!
# Information is unchanged by noise invisible to a left inverse

Embed a finite-input additive channel by a measurable additive map. Add
independent noise whose image under a measurable additive left inverse is
concentrated at zero. Projection recovers the original channel, while embedding
and convolution construct the larger channel. Data processing in both directions
gives exact equality, including singular residual noise and zero input weights.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace LpSelfSimilar.Entropy

/-- The projected convolution is exactly the original noise law. -/
theorem map_embedded_conv_of_invisible_noise {E F : Type*}
    [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    [AddMonoid F] [MeasurableSpace F] [MeasurableAdd₂ F]
    (ρ : Measure E) (τ : Measure F) [IsProbabilityMeasure ρ] [IsProbabilityMeasure τ]
    (f : E →+ F) (g : F →+ E) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) (hτ : τ.map g = Measure.dirac 0) :
    ((ρ.map f) ∗ τ).map g = ρ := by
  have : IsProbabilityMeasure (ρ.map f) := LpSelfSimilar.Probability.isProbabilityMeasure_map hf.aemeasurable
  rw [Measure.map_conv_addMonoidHom g hg, hτ, Measure.map_map hg hf]
  have he : g ∘ f = id := funext hgf
  rw [he, Measure.map_id, Measure.conv_dirac_zero]

/-- Independent noise invisible under a left inverse changes no finite-input information. -/
theorem additiveInformation_invisible_noise {ι E F : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    [AddMonoid F] [MeasurableSpace F] [MeasurableAdd₂ F]
    (p : PMF ι) (X : ι → E) (ρ : Measure E) (τ : Measure F)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure τ]
    (f : E →+ F) (g : F →+ E) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) (hτ : τ.map g = Measure.dirac 0) :
    additiveInformation p (fun i => f (X i)) ((ρ.map f) ∗ τ) = additiveInformation p X ρ := by
  have : IsProbabilityMeasure (ρ.map f) := LpSelfSimilar.Probability.isProbabilityMeasure_map hf.aemeasurable
  apply le_antisymm
  · exact (additiveInformation_conv_le p (fun i => f (X i)) (ρ.map f) τ).trans
      (additiveInformation_map_le p X ρ f hf f.map_add)
  · have h := additiveInformation_map_le p (fun i => f (X i)) ((ρ.map f) ∗ τ) g hg g.map_add
    rw [map_embedded_conv_of_invisible_noise ρ τ f g hf hg hgf hτ] at h
    have hgf' (x : E) : g (f x) = x := hgf x
    simpa only [hgf'] using h

end LpSelfSimilar.Entropy
