module

public import LpSelfSimilar.Entropy.FiniteChannel
public import LpSelfSimilar.Entropy.RelativeEntropyChain
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-!
Relative entropy of a finite channel against an arbitrary reference law.

The weighted divergence to a reference decomposes into the channel information
plus the divergence of its mixture to that reference (often called Donald's
identity). Finiteness of the latter gives the required integrability on every
positive-weight conditional law. The proof uses the actual mixture integral,
so neither a density nor an unproved differential-entropy identity is assumed.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InformationTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

lemma integrable_channel_of_integrable_mixture {ι E : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace E] (p : PMF ι)
    (κ : Kernel ι E) [IsMarkovKernel κ] {f : E → ℝ}
    (hf : Integrable f (κ ∘ₘ p.toMeasure)) {i : ι} (hi : p i ≠ 0) :
    Integrable f (κ i) := by
  have h := (dirac_absolutelyContinuous_pmf p hi).ae_le
    (Measure.ae_integrable_of_integrable_comp hf)
  simpa using h

lemma integral_mixture_eq_weighted_sum {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace E]
    (p : PMF ι) (κ : Kernel ι E) [IsMarkovKernel κ] {f : E → ℝ}
    (hf : Integrable f (κ ∘ₘ p.toMeasure)) :
    ∫ x, f x ∂(κ ∘ₘ p.toMeasure) = ∑ i, (p i).toReal * ∫ x, f x ∂κ i := by
  rw [Measure.comp_eq_comp_const_apply] at hf ⊢
  rw [Kernel.integral_comp hf]
  simp only [Kernel.const_apply, PMF.integral_eq_sum, smul_eq_mul]

/-- All positive-weight component divergences to the reference are finite. -/
lemma channel_reference_klDiv_ne_top {ι E : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [MeasurableSpace E] (p : PMF ι)
    (κ : Kernel ι E) [IsMarkovKernel κ] {ρ : Measure E} [IsProbabilityMeasure ρ]
    (hρ : klDiv (κ ∘ₘ p.toMeasure) ρ ≠ ∞) {i : ι} (hi : p i ≠ 0) :
    klDiv (κ i) ρ ≠ ∞ :=
  klDiv_chain_ne_top (channel_klDiv_ne_top p κ hi) (klDiv_ne_top_iff.mp hρ).1
    (integrable_channel_of_integrable_mixture p κ (klDiv_ne_top_iff.mp hρ).2 hi)

/-- Changing the reference adds the relative entropy of the actual mixture. -/
theorem finite_channel_reference_identity {ι E : Type*} [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace E]
    (p : PMF ι) (κ : Kernel ι E) [IsMarkovKernel κ]
    (ρ : Measure E) [IsProbabilityMeasure ρ]
    (hρ : klDiv (κ ∘ₘ p.toMeasure) ρ ≠ ∞) :
    ∑ i, (p i).toReal * (klDiv (κ i) ρ).toReal =
      (finiteInformation p κ).toReal + (klDiv (κ ∘ₘ p.toMeasure) ρ).toReal := by
  have hac := (klDiv_ne_top_iff.mp hρ).1
  have hint := (klDiv_ne_top_iff.mp hρ).2
  rw [finiteInformation_toReal, toReal_klDiv_of_measure_eq hac (by simp),
    integral_mixture_eq_weighted_sum p κ hint, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpi : p i = 0
  · simp [hpi]
  · rw [toReal_klDiv_chain (channel_klDiv_ne_top p κ hpi) hac
      (integrable_channel_of_integrable_mixture p κ hint hpi), mul_add]

end LpSelfSimilar.Entropy
