module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Entropy.FiniteAdditiveChannel

@[expose] public section

/-!
Information of a sum of independent finite signals.

The pair chain rule and translation invariance give
`I(X+Y; noise) = I(Y; noise) + I(X; Y+noise)`.
Here `I` always denotes the finite-input KL channel information, so every term
is finite even for singular noise. Applying data processing to the last term
proves that an entropy difference between two nested noise scales increases
when an independent finite summand is added. This is the finite-sum form of the
entropy-increment inequality needed in the algebraic-unit argument.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory InformationTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

lemma average_additive_channel {ι κ E : Type*} [Fintype ι] [Countable κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [AddMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (q : PMF κ) (X : ι → E) (Y : κ → E) (ρ : Measure E) [IsProbabilityMeasure ρ] :
    averageSecondChannel q ((additiveNoiseKernel ρ).comap
      (fun z : ι × κ ↦ X z.1 + Y z.2) (measurable_of_countable _)) =
      (additiveNoiseKernel ((q.toMeasure.map Y) ∗ ρ)).comap X
        (measurable_of_countable X) := by
  ext i : 1
  rw [averageSecondChannel_apply, Kernel.comap_apply, additiveNoiseKernel_apply]
  have hk : ((additiveNoiseKernel ρ).comap
      (fun z : ι × κ ↦ X z.1 + Y z.2) (measurable_of_countable _)).sectR i =
      (additiveNoiseKernel ρ).comap (fun j ↦ X i + Y j) (measurable_of_countable _) := by
    ext j : 1
    rfl
  rw [hk, kernel_comap_comp_measure, additiveNoiseKernel_comp]
  have hm : q.toMeasure.map (fun j ↦ X i + Y j) =
      (q.toMeasure.map Y).map (fun x ↦ X i + x) :=
    (Measure.map_map (measurable_const.add measurable_id) (measurable_of_countable Y)).symm
  rw [hm, ← Measure.dirac_conv, Measure.conv_assoc, Measure.dirac_conv]

/-- Exact finite-sum information chain rule for arbitrary probability noise. -/
theorem additiveInformation_pair_chain {ι κ E : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [AddGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (p : PMF ι) (q : PMF κ) (X : ι → E) (Y : κ → E)
    (ρ : Measure E) [IsProbabilityMeasure ρ] :
    additiveInformation (pairPMF p q) (fun z ↦ X z.1 + Y z.2) ρ =
      additiveInformation p X ((q.toMeasure.map Y) ∗ ρ) + additiveInformation q Y ρ := by
  unfold additiveInformation
  rw [finiteInformation_pair_chain, average_additive_channel]
  congr 1
  have hs (i : ι) : (finiteInformation q
      (((additiveNoiseKernel ρ).comap (fun z : ι × κ ↦ X z.1 + Y z.2)
        (measurable_of_countable _)).sectR i)).toReal = additiveInformation q Y ρ := by
    change additiveInformation q (fun j ↦ X i + Y j) ρ = _
    exact additiveInformation_translate q Y ρ (X i)
  simp_rw [hs]
  simpa only [integral_const, probReal_univ, one_smul, smul_eq_mul, one_mul,
    additiveInformation] using
    (PMF.integral_eq_sum p (fun _ ↦ additiveInformation q Y ρ)).symm

/-- An independent finite summand increases the information difference between
nested additive noise laws. The added noise may be singular or degenerate. -/
theorem additiveInformation_noise_difference_mono {ι κ E : Type*}
    [Fintype ι] [Fintype κ]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [AddGroup E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (p : PMF ι) (q : PMF κ) (X : ι → E) (Y : κ → E)
    (ρ τ : Measure E) [IsProbabilityMeasure ρ] [IsProbabilityMeasure τ] :
    additiveInformation q Y ρ - additiveInformation q Y (ρ ∗ τ) ≤
      additiveInformation (pairPMF p q) (fun z ↦ X z.1 + Y z.2) ρ -
        additiveInformation (pairPMF p q) (fun z ↦ X z.1 + Y z.2) (ρ ∗ τ) := by
  have : IsProbabilityMeasure (q.toMeasure.map Y) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (measurable_of_countable Y).aemeasurable
  rw [additiveInformation_pair_chain, additiveInformation_pair_chain,
    ← Measure.conv_assoc]
  have h := additiveInformation_conv_le p X ((q.toMeasure.map Y) ∗ ρ) τ
  linarith

end LpSelfSimilar.Entropy
