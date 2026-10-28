module

public import LpSelfSimilar.Gaussian.ApproximateIdentity
public import LpSelfSimilar.Analysis.BoundedTestLimit
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section

/-!
An L1 limit of Gaussian smoothings represents the original measure. Bounded
continuous tests identify the independently proved weak and L1 limits, and the
withDensity formula is justified for the chosen nonnegative integrable function.
-/

open MeasureTheory MeasureTheory.Measure Real Filter
open scoped Topology NNReal ENNReal BoundedContinuousFunction

namespace LpSelfSimilar.Gaussian

/-- The original measure equals Lebesgue measure weighted by the L1 limit. -/
theorem eq_withDensity_of_smoothing_L1_limit (μ : Measure ℝ) [IsFiniteMeasure μ]
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    {f : ℝ → ℝ} (hf : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    (hlim : Tendsto (fun n : ℕ ↦ ∫ x,
      |smooth μ ((r n) ^ 2) x - f x|) atTop (𝓝 0)) :
    μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  haveI : IsFiniteMeasure (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ hf0)]
    exact ENNReal.ofReal_ne_top
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  have hweak := tendsto_integral_bounded_test_smooth μ φ hr hrlim
  have hstrong := tendsto_integral_bounded_mul_of_L1
    (fun n ↦ integrable_smooth μ (sq_pos_of_pos (hr n))) hf
    φ.continuous.measurable.aestronglyMeasurable (norm_nonneg φ)
    (ae_of_all _ (fun x ↦ φ.norm_coe_le_norm x)) hlim
  have he := tendsto_nhds_unique hweak hstrong
  rw [he]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ae_of_all _ (fun x ↦ ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun x ↦ mul_comm _ _)

end LpSelfSimilar.Gaussian
