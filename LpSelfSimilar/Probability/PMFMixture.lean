module

public import LpSelfSimilar.Probability.FiniteMixture

@[expose] public section

/-!
Finite mixtures indexed by an actual PMF. The integral formula identifies finite
weighted sums with expectations on the conditioning space. Null outcomes are
allowed and have zero contribution.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace LpSelfSimilar

noncomputable def pmfMixture {Ω : Type*} [Fintype Ω] (p : PMF Ω) (μ : Ω → Measure ℝ) : Measure ℝ :=
  finiteMixture (fun ω ↦ (p ω).toNNReal) μ

lemma pmf_weights_sum {Ω : Type*} [Fintype Ω] (p : PMF Ω) : ∑ ω, (p ω).toNNReal = 1 := by
  apply ENNReal.coe_injective
  rw [ENNReal.coe_finset_sum]
  simp only [ENNReal.coe_toNNReal (p.apply_ne_top _), ENNReal.coe_one]
  exact (tsum_fintype (f := p)).symm.trans p.tsum_coe

instance pmfMixture_probability {Ω : Type*} [Fintype Ω] (p : PMF Ω) (μ : Ω → Measure ℝ)
    [∀ ω, IsProbabilityMeasure (μ ω)] : IsProbabilityMeasure (pmfMixture p μ) :=
  finiteMixture_isProbabilityMeasure _ (pmf_weights_sum p) μ

lemma pmf_sum_eq_integral {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (f : Ω → ℝ) : (∑ ω, (p ω).toReal * f ω) = ∫ ω, f ω ∂p.toMeasure := by
  simpa only [smul_eq_mul] using (PMF.integral_eq_sum p f).symm

end LpSelfSimilar
