module

public import LpSelfSimilar.Analysis.AbsoluteContinuity

@[expose] public section

/-! A nonnegative integrable representing density equals the canonical density almost everywhere. -/

open MeasureTheory

namespace LpSelfSimilar

lemma density_ae_eq_of_representation {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} [SigmaFinite μ] {f : X → ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x)
    (hrep : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) :
    density ν μ =ᵐ[μ] f := by
  rw [hrep]
  filter_upwards [Measure.rnDeriv_withDensity₀ μ
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal] with x hx
  change ((μ.withDensity (fun x ↦ ENNReal.ofReal (f x))).rnDeriv μ x).toReal = f x
  rw [hx, ENNReal.toReal_ofReal (hf0 x)]

end LpSelfSimilar
