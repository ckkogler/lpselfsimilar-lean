module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Kernel.Composition.Lemmas

@[expose] public section

/-!
The Markov kernel for adding an independent noise vector.

This construction works on any measurable additive monoid. Its composition with
a probability law is the actual convolution, and composing two noise kernels
adds their independent noises. No density or nondegeneracy hypothesis occurs;
this includes singular Gaussian noise arising from a covariance difference.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace LpSelfSimilar

noncomputable def additiveNoiseKernel {E : Type*} [AddMonoid E] [MeasurableSpace E]
    (ρ : Measure E) : Kernel E E :=
  (Kernel.id ×ₖ Kernel.const E ρ).map (fun z : E × E ↦ z.1 + z.2)

instance additiveNoiseKernel_isMarkov {E : Type*} [AddMonoid E] [MeasurableSpace E]
    [MeasurableAdd₂ E] (ρ : Measure E) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (additiveNoiseKernel ρ) := by
  unfold additiveNoiseKernel
  exact Kernel.IsMarkovKernel.map _ measurable_add

lemma additiveNoiseKernel_apply {E : Type*} [AddMonoid E] [MeasurableSpace E]
    [MeasurableAdd₂ E] (ρ : Measure E) [SFinite ρ] (x : E) :
    additiveNoiseKernel ρ x = ρ.map (fun y ↦ x + y) := by
  rw [additiveNoiseKernel, Kernel.map_apply _ measurable_add, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply]
  exact Measure.dirac_conv x ρ

lemma additiveNoiseKernel_comp {E : Type*} [AddMonoid E] [MeasurableSpace E]
    [MeasurableAdd₂ E] (μ ρ : Measure E) [SFinite μ] [SFinite ρ] :
    additiveNoiseKernel ρ ∘ₘ μ = μ ∗ ρ := by
  rw [additiveNoiseKernel, ← Measure.map_comp μ _ measurable_add,
    ← Measure.compProd_eq_comp_prod, Measure.compProd_const]
  rfl

lemma additiveNoiseKernel_comp_kernel {E : Type*} [AddMonoid E] [MeasurableSpace E]
    [MeasurableAdd₂ E] (ρ τ : Measure E) [IsProbabilityMeasure ρ]
    [IsProbabilityMeasure τ] :
    additiveNoiseKernel τ ∘ₖ additiveNoiseKernel ρ = additiveNoiseKernel (ρ ∗ τ) := by
  ext x : 1
  rw [Kernel.comp_apply, additiveNoiseKernel_comp, additiveNoiseKernel_apply,
    ← Measure.dirac_conv, Measure.conv_assoc, Measure.dirac_conv,
    additiveNoiseKernel_apply]

end LpSelfSimilar
