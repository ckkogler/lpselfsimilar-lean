module

public import LpSelfSimilar.Analysis.LogCoshBound
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

/-!
# Regularity and integrability of log cosh

The explicit derivative is tanh, and log cosh lies between zero and the
absolute value. Consequently an integrable real signal remains integrable
after applying log cosh. These bounds justify the Gaussian information
integrals and their local dominated differentiation.
-/

open MeasureTheory Real

namespace LpSelfSimilar.Analysis

@[fun_prop] theorem continuous_log_cosh : Continuous (fun x : ℝ => log (cosh x)) :=
  Real.continuous_cosh.log (fun x => (cosh_pos x).ne')

theorem hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun y : ℝ => log (cosh y)) (tanh x) x := by
  simpa only [tanh_eq_sinh_div_cosh] using (hasDerivAt_cosh x).log (cosh_pos x).ne'

theorem log_cosh_nonneg (x : ℝ) : 0 ≤ log (cosh x) := log_nonneg (one_le_cosh x)

theorem log_cosh_le_abs (x : ℝ) : log (cosh x) ≤ |x| := by
  apply (log_le_iff_le_exp (cosh_pos x)).mpr
  rw [cosh_eq]
  have hp := exp_le_exp.mpr (le_abs_self x)
  have hm := exp_le_exp.mpr (neg_le_abs x)
  linarith

theorem abs_log_cosh_le_abs (x : ℝ) : |log (cosh x)| ≤ |x| := by
  rw [abs_of_nonneg (log_cosh_nonneg x)]
  exact log_cosh_le_abs x

/-- Applying log cosh to an integrable signal gives an actual integrable function. -/
theorem integrable_log_cosh {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f : E → ℝ} (hf : Integrable f μ) : Integrable (fun x => log (cosh (f x))) μ := by
  apply hf.norm.mono' (continuous_log_cosh.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using abs_log_cosh_le_abs (f x))

end LpSelfSimilar.Analysis
