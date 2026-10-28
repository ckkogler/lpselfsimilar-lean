module

public import LpSelfSimilar.Gaussian.LowFrequencyConstant

@[expose] public section

/-!
# Integrating the two low-frequency Fourier errors

The zeroth and first derivative bounds share a Gaussian factor. Squaring and
adding gives one explicitly integrable polynomial majorant. Restricting to any
measurable frequency set only decreases its integral. Measurability and the
majorant supply integrability, so no unproved integrability input is needed.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Gaussian

/-- The two pointwise Fourier error bounds imply the exact squared-energy majorant. -/
theorem sq_errors_le_lowFrequencyGaussianEnergy {χ u : ℝ} {z w : ℂ}
    (hχ : 0 ≤ χ)
    (hz : ‖z‖ ≤ χ / 6 * u ^ 4 * Real.exp (-(u ^ 2) / 2))
    (hw : ‖w‖ ≤ χ / 6 * (|u| ^ 5 + 4 * |u| ^ 3) * Real.exp (-(u ^ 2) / 2)) :
    ‖z‖ ^ 2 + ‖w‖ ^ 2 ≤
      χ ^ 2 / 36 * ((u ^ 10 + 9 * u ^ 8 + 16 * u ^ 6) * Real.exp (-(u ^ 2))) := by
  have h := add_le_add (pow_le_pow_left₀ (norm_nonneg z) hz 2)
    (pow_le_pow_left₀ (norm_nonneg w) hw 2)
  refine h.trans_eq ?_
  have ha (k : ℕ) : |u| ^ (2 * k) = u ^ (2 * k) := by
    rw [pow_mul, sq_abs, ← pow_mul]
  have he : Real.exp (-(u ^ 2) / 2) ^ 2 = Real.exp (-(u ^ 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ = χ ^ 2 / 36 * (u ^ 8 + |u| ^ 10 + 8 * |u| ^ 8 + 16 * |u| ^ 6) *
        Real.exp (-(u ^ 2) / 2) ^ 2 := by ring
    _ = _ := by rw [ha 5, ha 4, ha 3, he]; ring

/-- Both errors are square integrable on a measurable set where their Gaussian bounds hold. -/
theorem integrableOn_sq_errors_of_lowFrequencyGaussianBounds
    {χ : ℝ} {s : Set ℝ} {f g : ℝ → ℂ} (hχ : 0 ≤ χ) (hs : MeasurableSet s)
    (hf : AEStronglyMeasurable f (volume.restrict s))
    (hg : AEStronglyMeasurable g (volume.restrict s))
    (h0 : ∀ u ∈ s, ‖f u‖ ≤ χ / 6 * u ^ 4 * Real.exp (-(u ^ 2) / 2))
    (h1 : ∀ u ∈ s, ‖g u‖ ≤ χ / 6 * (|u| ^ 5 + 4 * |u| ^ 3) * Real.exp (-(u ^ 2) / 2)) :
    IntegrableOn (fun u => ‖f u‖ ^ 2 + ‖g u‖ ^ 2) s := by
  refine (integrable_lowFrequencyGaussianEnergy.const_mul (χ ^ 2 / 36)).integrableOn.mono'
    ((hf.norm.pow 2).add (hg.norm.pow 2)) ?_
  apply (ae_restrict_iff' hs).2
  exact ae_of_all _ (fun u hu => by
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact sq_errors_le_lowFrequencyGaussianEnergy hχ (h0 u hu) (h1 u hu))

/-- Weighted integration gives the exact coefficient, for any measurable low-frequency set. -/
theorem half_integral_sq_errors_le_lowFrequencyGaussianConstant
    {χ : ℝ} {s : Set ℝ} {f g : ℝ → ℂ} (hχ : 0 ≤ χ) (hs : MeasurableSet s)
    (hf : AEStronglyMeasurable f (volume.restrict s))
    (hg : AEStronglyMeasurable g (volume.restrict s))
    (h0 : ∀ u ∈ s, ‖f u‖ ≤ χ / 6 * u ^ 4 * Real.exp (-(u ^ 2) / 2))
    (h1 : ∀ u ∈ s, ‖g u‖ ≤ χ / 6 * (|u| ^ 5 + 4 * |u| ^ 3) * Real.exp (-(u ^ 2) / 2)) :
    (1 / 2 : ℝ) * (∫ u in s, ‖f u‖ ^ 2 + ‖g u‖ ^ 2) ≤
      χ ^ 2 * lowFrequencyGaussianConstant ^ 2 := by
  have hi := integrableOn_sq_errors_of_lowFrequencyGaussianBounds hχ hs hf hg h0 h1
  have hm := integrable_lowFrequencyGaussianEnergy.const_mul (χ ^ 2 / 36)
  have hle := setIntegral_mono_on hi hm.integrableOn hs
    (fun u hu => sq_errors_le_lowFrequencyGaussianEnergy hχ (h0 u hu) (h1 u hu))
  have hglobal := setIntegral_le_integral (s := s) hm (ae_of_all _ (fun u => by positivity))
  have h := mul_le_mul_of_nonneg_left (hle.trans hglobal) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine h.trans_eq ?_
  rw [integral_const_mul, integral_lowFrequencyGaussianEnergy,
    lowFrequencyGaussianConstant_eq, Real.sq_sqrt (by positivity)]
  ring

end LpSelfSimilar.Gaussian
