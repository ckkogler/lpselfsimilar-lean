module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

/-!
Passing L1 bounds to an almost-everywhere pointwise limit. This is Fatou's
lemma with a convergent real upper bound, suitable for finite approximations of
probability laws. The integrals and their bounds are not assumed to converge.
-/

open MeasureTheory Filter
open scoped Topology

namespace LpSelfSimilar

lemma integral_abs_le_of_tendsto {μ : Measure ℝ} {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hf : Integrable f μ)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x)))
    {C : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hC : Tendsto C atTop (𝓝 c))
    (hb : ∀ n, (∫ x, |F n x| ∂μ) ≤ C n) : (∫ x, |f x| ∂μ) ≤ c := by
  have hh := lintegral_enorm_le_liminf_of_tendsto ht
    (fun n ↦ (hF n).aestronglyMeasurable.aemeasurable.enorm)
  rw [← ofReal_integral_norm_eq_lintegral_enorm hf] at hh
  have hm : Filter.liminf (fun n ↦ ∫⁻ x, ‖F n x‖ₑ ∂μ) atTop ≤
      Filter.liminf (fun n ↦ ENNReal.ofReal (C n)) atTop := by
    refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
    apply Eventually.of_forall
    intro n
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF n)]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hb n)
  have he := ((ENNReal.continuous_ofReal.tendsto c).comp hC).liminf_eq
  change Filter.liminf (fun n ↦ ENNReal.ofReal (C n)) atTop = ENNReal.ofReal c at he
  rw [he] at hm
  exact (ENNReal.ofReal_le_ofReal_iff hc).mp (by
    simpa only [Real.norm_eq_abs] using hh.trans hm)

end LpSelfSimilar
