module

public import LpSelfSimilar.Analysis.GeometricQuadrature

@[expose] public section

/-!
# Keeping the final geometric tail as one atom

For a function bounded by one, replacing its integral over `[0,t]` by the mass
`t` at the endpoint costs at most `2t`. Combining this with finite geometric
quadrature gives the exact tail error used by phase averaging.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- Moving an interval of mass `t` to its endpoint costs at most `2t` for a bounded function. -/
theorem abs_tail_endpoint_error_le {f : ℝ → ℝ} (hf : ∀ x, |f x| ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) : |t * f t - ∫ x in (0 : ℝ)..t, f x| ≤ 2 * t := by
  have hi : |∫ x in (0 : ℝ)..t, f x| ≤ t := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := 1)
      (fun x _ ↦ (show ‖f x‖ ≤ (1 : ℝ) by simpa only [Real.norm_eq_abs] using hf x))
    simpa only [Real.norm_eq_abs, sub_zero, one_mul, abs_of_nonneg ht] using h
  have he : |t * f t| ≤ t := by
    rw [abs_mul, abs_of_nonneg ht]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hf t) ht
  exact (abs_sub (t * f t) _).trans (by linarith)

/-- Finite quadrature including an atom for the remaining geometric mass. -/
theorem abs_geometric_average_sub_integral_le {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (hbound : ∀ x, |f x| ≤ 1)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (N : ℕ) :
    |((∑ k ∈ Finset.range N, (1 - θ) * θ ^ k * f (θ ^ k)) + θ ^ N * f (θ ^ N)) -
        ∫ x in (0 : ℝ)..1, f x| ≤
      (K : ℝ) / 2 * ((1 - θ) / (1 + θ)) + 2 * θ ^ N := by
  have hquad := abs_geometric_quadrature_error_le hf hθ0 hθ1 N
  have htail := abs_tail_endpoint_error_le hbound (pow_nonneg hθ0 N)
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.continuous.intervalIntegrable 0 (θ ^ N)) (hf.continuous.intervalIntegrable (θ ^ N) 1)
  have he : ((∑ k ∈ Finset.range N, (1 - θ) * θ ^ k * f (θ ^ k)) + θ ^ N * f (θ ^ N)) -
      (∫ x in (0 : ℝ)..1, f x) =
      ((∑ k ∈ Finset.range N, (1 - θ) * θ ^ k * f (θ ^ k)) - ∫ x in θ ^ N..1, f x) +
        (θ ^ N * f (θ ^ N) - ∫ x in (0 : ℝ)..θ ^ N, f x) := by linarith
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hquad htail)

end LpSelfSimilar.Analysis
