module

public import LpSelfSimilar.Analysis.NonnegativeLp

@[expose] public section

/-!
A measurable extended-valued representative of an integrable real density,
with its mass and power integral retained. This allows Tonelli arguments to use
measurable kernels without strengthening the original density hypotheses.
-/

open MeasureTheory
open scoped ENNReal

namespace LpSelfSimilar

lemma exists_measurable_ennreal_density {f : ℝ → ℝ} (hf : Integrable f volume)
    (hn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 0 < p)
    (hLp : MemLp f (ENNReal.ofReal p) volume) :
    ∃ F : ℝ → ℝ≥0∞, Measurable F ∧
      (fun x ↦ ENNReal.ofReal (f x)) =ᵐ[volume] F ∧
      (∫⁻ x, F x) < ∞ ∧ (∫⁻ x, F x ^ p) < ∞ := by
  let hmeas := hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  refine ⟨hmeas.mk _, hmeas.measurable_mk, hmeas.ae_eq_mk, ?_, ?_⟩
  · rw [← lintegral_congr_ae hmeas.ae_eq_mk]
    have h := hf.hasFiniteIntegral
    simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal (hn _)] using h
  · have he : (∫⁻ x, ENNReal.ofReal (f x) ^ p) =
        ∫⁻ x, hmeas.mk _ x ^ p := lintegral_congr_ae (hmeas.ae_eq_mk.fun_comp (fun x ↦ x ^ p))
    rw [← he]
    exact (memLp_nonneg_iff_power_integral hp hf.aestronglyMeasurable hn).mp hLp

end LpSelfSimilar
