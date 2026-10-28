module

public import LpSelfSimilar.Analysis.EndpointQuadrature
public import LpSelfSimilar.Analysis.GeometricWeights

@[expose] public section

/-!
# Finite geometric quadrature

Sum the sharp endpoint error over the intervals between successive powers of
`theta`. The integrals telescope exactly, even before taking any limit. The
squared-length bound gives the uniform geometric quadrature error.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- Integrals over successive geometric intervals telescope exactly. -/
theorem sum_integral_geometric_intervals {f : ℝ → ℝ} (hf : Continuous f)
    (θ : ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∫ x in θ ^ (k + 1)..θ ^ k, f x) = ∫ x in θ ^ N..1, f x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    simpa only [add_comm] using intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable (θ ^ (N + 1)) (θ ^ N)) (hf.intervalIntegrable (θ ^ N) 1)

/-- Finite geometric right-endpoint quadrature with its sharp uniform error. -/
theorem abs_geometric_quadrature_error_le {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (N : ℕ) :
    |(∑ k ∈ Finset.range N, (1 - θ) * θ ^ k * f (θ ^ k)) - ∫ x in θ ^ N..1, f x| ≤
      (K : ℝ) / 2 * ((1 - θ) / (1 + θ)) := by
  have he : (∑ k ∈ Finset.range N, (1 - θ) * θ ^ k * f (θ ^ k)) -
      (∫ x in θ ^ N..1, f x) =
      ∑ k ∈ Finset.range N, ((θ ^ k - θ ^ (k + 1)) * f (θ ^ k) -
        ∫ x in θ ^ (k + 1)..θ ^ k, f x) := by
    rw [Finset.sum_sub_distrib, sum_integral_geometric_intervals hf.continuous θ N]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ]
    ring
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.range N, |(θ ^ k - θ ^ (k + 1)) * f (θ ^ k) -
        ∫ x in θ ^ (k + 1)..θ ^ k, f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, (K : ℝ) / 2 * (θ ^ k - θ ^ (k + 1)) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      apply abs_right_endpoint_quadrature_error_le hf
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hθ0 k) hθ1.le
    _ = (K : ℝ) / 2 * ∑ k ∈ Finset.range N, (θ ^ k - θ ^ (k + 1)) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ (K : ℝ) / 2 * ((1 - θ) / (1 + θ)) :=
      mul_le_mul_of_nonneg_left (sum_sq_geometric_gaps_le hθ0 hθ1 N) (by positivity)

end LpSelfSimilar.Analysis
