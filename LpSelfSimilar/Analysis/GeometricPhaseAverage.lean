module

public import LpSelfSimilar.Analysis.GeometricQuadratureTail
public import LpSelfSimilar.Analysis.CosineAverage
public import LpSelfSimilar.Analysis.GeometricPhaseConstants
public import LpSelfSimilar.Analysis.GeometricPhaseLength

@[expose] public section

/-!
# Finite geometric phase averaging

The exact geometric probability vector, including its remaining tail as one
atom, gives cancellation at least `3/5` throughout the prescribed frequency band.
Finite quadrature proves the estimate directly. The stronger intermediate margin
`0.6585` and the length `ceil(log(10000)/(-log theta))` are retained.
-/

open MeasureTheory Set
open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- The finite geometric cosine average differs from its unit-interval average by the stated error. -/
theorem geometric_cosine_average_le {θ y : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hy : 1 / 2 ≤ y) (N : ℕ) :
    (∑ k : Fin (N + 1), geometricWeight θ N k * Real.cos (2 * Real.pi * y * θ ^ (k : ℕ))) ≤
      1 / (2 * Real.pi) + Real.pi * y * ((1 - θ) / (1 + θ)) + 2 * θ ^ N := by
  have hc : 0 ≤ 2 * Real.pi * y := by positivity
  have hq := abs_geometric_average_sub_integral_le (lipschitzWith_cos_mul (2 * Real.pi * y))
    (fun x ↦ Real.abs_cos_le_one _) hθ0 hθ1 N
  simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hc] at hq
  have hupper := (abs_le.mp hq).2
  have hi := integral_cos_two_pi_mul_le hy
  rw [sum_geometricWeight_mul θ N (fun k ↦ Real.cos (2 * Real.pi * y * θ ^ k))]
  nlinarith

/-- The strict numerical phase margin for any tail no larger than one ten-thousandth. -/
theorem geometric_phase_average_gt_margin {θ y : ℝ}
    (hθ : Real.exp (-1 / 70) ≤ θ) (hθ1 : θ < 1)
    (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 8 / θ) (N : ℕ)
    (htail : θ ^ N ≤ (1 / 10000 : ℝ)) :
    (6585 / 10000 : ℝ) < ∑ k : Fin (N + 1), geometricWeight θ N k *
      (1 - Real.cos (2 * Real.pi * y * θ ^ (k : ℕ))) := by
  have hθ0 : 0 < θ := (Real.exp_pos _).trans_le hθ
  have havg := geometric_cosine_average_le hθ0.le hθ1 hy0 N
  have herr : Real.pi * y * ((1 - θ) / (1 + θ)) ≤
      8 * Real.pi * (1 - θ) / (θ * (1 + θ)) := by
    calc
      _ ≤ Real.pi * (8 / θ) * ((1 - θ) / (1 + θ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy1 Real.pi_pos.le)
          (div_nonneg (sub_nonneg.mpr hθ1.le) (by positivity))
      _ = _ := by field_simp
  have he : (∑ k : Fin (N + 1), geometricWeight θ N k *
      (1 - Real.cos (2 * Real.pi * y * θ ^ (k : ℕ)))) =
      1 - ∑ k : Fin (N + 1), geometricWeight θ N k * Real.cos (2 * Real.pi * y * θ ^ (k : ℕ)) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, sum_geometricWeight_eq_one]
  rw [he]
  have hm := geometric_phase_margin_gt hθ hθ1.le
  linarith

/-- Geometric phase averaging with the exact finite stopping length and coefficient `3/5`. -/
theorem geometric_phase_average_ge_three_fifths {θ y : ℝ}
    (hθ : Real.exp (-1 / 70) ≤ θ) (hθ1 : θ < 1)
    (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 8 / θ) :
    (3 / 5 : ℝ) ≤ ∑ k : Fin (geometricPhaseLength θ + 1),
      geometricWeight θ (geometricPhaseLength θ) k *
        (1 - Real.cos (2 * Real.pi * y * θ ^ (k : ℕ))) := by
  have hθ0 : 0 < θ := (Real.exp_pos _).trans_le hθ
  have h := geometric_phase_average_gt_margin hθ hθ1 hy0 hy1 (geometricPhaseLength θ)
    (pow_geometricPhaseLength_le hθ0 hθ1)
  linarith

/-- Logarithmic-gap form used directly by the working regularity criterion. -/
theorem geometric_phase_average_ge_of_log_gap {θ y : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 70)
    (hy0 : 1 / 2 ≤ y) (hy1 : y ≤ 8 / θ) :
    (3 / 5 : ℝ) ≤ ∑ k : Fin (geometricPhaseLength θ + 1),
      geometricWeight θ (geometricPhaseLength θ) k *
        (1 - Real.cos (2 * Real.pi * y * θ ^ (k : ℕ))) := by
  have hθ : Real.exp (-1 / 70) ≤ θ := by
    rw [← Real.exp_log hθ0]
    apply Real.exp_le_exp.mpr
    linarith
  exact geometric_phase_average_ge_three_fifths hθ hθ1 hy0 hy1

end LpSelfSimilar.Analysis
