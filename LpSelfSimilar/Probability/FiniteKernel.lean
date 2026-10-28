module

public import LpSelfSimilar.Probability.PMFMixture
public import Mathlib.Probability.Kernel.Composition.CompNotation

@[expose] public section

/-!
A finite family of actual laws, regarded as a measurable probability kernel.
Its composition with a PMF is exactly the finite mixture already used in the
library. This interface transfers general kernel estimates to finite conditioning.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory

namespace LpSelfSimilar

/-- Composition of a finite kernel is the actual PMF-weighted measure sum. -/
lemma finite_kernel_comp_eq_pmfMixture {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (κ : Kernel Ω ℝ) :
    κ ∘ₘ p.toMeasure = pmfMixture p κ := by
  ext s hs
  rw [Measure.bind_apply hs κ.aemeasurable, lintegral_fintype]
  simp only [pmfMixture, finiteMixture, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, ENNReal.coe_toNNReal (p.apply_ne_top _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

end LpSelfSimilar
