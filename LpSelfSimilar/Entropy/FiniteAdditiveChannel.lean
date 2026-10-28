module

public import LpSelfSimilar.Entropy.ChannelInvariance
public import LpSelfSimilar.Analysis.AdditiveNoiseKernel
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

@[expose] public section

/-!
Finite-signal information through an additive noise channel.

All information is in nats and is defined using finite KL divergences, rather
than a formal difference of possibly undefined differential entropies. It lies
between zero and the input entropy, is unchanged by translating the signal,
and decreases upon adding independent noise. These facts hold for arbitrary
probability noise on a measurable additive group, including singular laws.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InformationTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

noncomputable def additiveInformation {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [AddMonoid E] [MeasurableSpace E]
    (p : PMF ι) (X : ι → E) (ρ : Measure E) : ℝ :=
  (finiteInformation p ((additiveNoiseKernel ρ).comap X (measurable_of_countable X))).toReal

lemma additiveInformation_nonneg {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [AddMonoid E] [MeasurableSpace E]
    (p : PMF ι) (X : ι → E) (ρ : Measure E) : 0 ≤ additiveInformation p X ρ :=
  ENNReal.toReal_nonneg

lemma additiveInformation_le_entropy {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [AddMonoid E] [MeasurableSpace E]
    [MeasurableAdd₂ E] (p : PMF ι) (X : ι → E) (ρ : Measure E)
    [IsProbabilityMeasure ρ] : additiveInformation p X ρ ≤ finiteEntropy p (Set.toFinite _) :=
  finiteInformation_toReal_le_entropy p _

lemma kernel_comap_comp_measure {ι E F : Type*} [MeasurableSpace ι]
    [MeasurableSpace E] [MeasurableSpace F] (μ : Measure ι)
    (K : Kernel E F) {f : ι → E} (hf : Measurable f) :
    K.comap f hf ∘ₘ μ = K ∘ₘ μ.map f := by
  rw [← Measure.deterministic_comp_eq_map hf, Measure.comp_assoc,
    Kernel.comp_deterministic_eq_comap]

/-- The output is exactly the convolution of the actual signal law with noise. -/
lemma additive_channel_mixture {ι E : Type*} [Countable ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [AddMonoid E] [MeasurableSpace E]
    [MeasurableAdd₂ E] (p : PMF ι) (X : ι → E) (ρ : Measure E)
    [IsProbabilityMeasure ρ] :
    (additiveNoiseKernel ρ).comap X (measurable_of_countable X) ∘ₘ p.toMeasure =
      (p.toMeasure.map X) ∗ ρ := by
  rw [kernel_comap_comp_measure, additiveNoiseKernel_comp]

/-- Adding independent noise cannot increase finite-signal information. -/
theorem additiveInformation_conv_le {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [AddMonoid E] [MeasurableSpace E]
    [MeasurableAdd₂ E] (p : PMF ι) (X : ι → E) (ρ τ : Measure E)
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure τ] :
    additiveInformation p X (ρ ∗ τ) ≤ additiveInformation p X ρ := by
  let K := (additiveNoiseKernel ρ).comap X (measurable_of_countable X)
  have he : additiveNoiseKernel τ ∘ₖ K =
      (additiveNoiseKernel (ρ ∗ τ)).comap X (measurable_of_countable X) := by
    rw [← additiveNoiseKernel_comp_kernel ρ τ]
    ext i : 1
    rfl
  have h := finiteInformation_comp_le p K (additiveNoiseKernel τ)
  rw [he] at h
  exact ENNReal.toReal_mono (finiteInformation_ne_top p K) h

lemma additive_channel_translate {ι E : Type*} [MeasurableSpace ι]
    [AddGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (X : ι → E) (hX : Measurable X) (ρ : Measure E) [IsProbabilityMeasure ρ] (a : E) :
    (additiveNoiseKernel ρ).comap (fun i ↦ a + X i) (measurable_const.add hX) =
      ((additiveNoiseKernel ρ).comap X hX).map (MeasurableEquiv.addLeft a) := by
  ext i : 1
  rw [Kernel.map_apply _ (MeasurableEquiv.addLeft a).measurable]
  simp only [Kernel.comap_apply, additiveNoiseKernel_apply]
  rw [Measure.map_map (MeasurableEquiv.addLeft a).measurable (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply, MeasurableEquiv.coe_addLeft, add_assoc]

/-- Translating a finite signal changes neither its information nor its noise. -/
theorem additiveInformation_translate {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [AddGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (p : PMF ι) (X : ι → E) (ρ : Measure E) [IsProbabilityMeasure ρ] (a : E) :
    additiveInformation p (fun i ↦ a + X i) ρ = additiveInformation p X ρ := by
  unfold additiveInformation
  rw [additive_channel_translate X (measurable_of_countable X) ρ a,
    finiteInformation_map_measurableEquiv]

end LpSelfSimilar.Entropy
