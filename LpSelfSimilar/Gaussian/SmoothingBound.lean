module

public import LpSelfSimilar.Gaussian.SmoothingMeasure
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
A universal bound for smoothing a probability measure at variance one. It is
the bounded approximant used in the rational higher-integrability argument.
-/

open MeasureTheory Real

namespace LpSelfSimilar.Gaussian

lemma kernel_one_le_half (x : ℝ) : kernel 1 x ≤ 1 / 2 := by
  have hs : (2 : ℝ) ≤ sqrt (2 * Real.pi) := by
    apply (le_sqrt (by norm_num) (by positivity)).mpr
    nlinarith [pi_gt_three]
  have hp := kernel_le_peak (by norm_num : (0 : ℝ) < 1) x
  simp only [mul_one] at hp
  apply hp.trans
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hs

/-- Every probability measure has variance-one Gaussian smoothing bounded by 1/2. -/
theorem smooth_one_le_half (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    smooth μ 1 x ≤ 1 / 2 := by
  have h := integral_mono (integrable_kernel_translate μ (by norm_num : (0 : ℝ) < 1) x)
    (integrable_const (1 / 2 : ℝ)) (fun z ↦ kernel_one_le_half (x - z))
  convert h using 1 <;> try rfl
  simp

end LpSelfSimilar.Gaussian
