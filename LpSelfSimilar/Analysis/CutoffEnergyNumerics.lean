module

public import LpSelfSimilar.Analysis.ExponentialTailNumerics
public import LpSelfSimilar.Analysis.MixedGaussianTail

@[expose] public section

/-!
# The numerical high-frequency cutoff energy margin

The exact integrated bound splits, after division by the squared gap, into
two pure inverse-power Gaussian tails and a mixed term from the cutoff width.
Their proved endpoint estimates give a squared ratio below 10^(-40).
-/

namespace LpSelfSimilar.Analysis

/-- The exact high-frequency cutoff energy has squared gap ratio below 10^(-40). -/
theorem cutoff_gaussian_energy_div_sq_lt {x ε : ℝ} (hx : 0 < x) (hxR : x ≤ 1 / 250)
    (hε : 0 < ε)
    (hwidth : 1 / ε ≤ 100000 / (150 * Real.sqrt (2 * x)) *
      Real.exp (1 / Real.sqrt (2 * x))) :
    (Real.exp (-1 / (4 * x)) ^ 2 *
      ((2 / (x * Real.sqrt x)) * (1 + 18 / x) + 6 * x * Real.sqrt x / ε)) / x ^ 2 <
      1 / (10 : ℝ) ^ 40 := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hsq := Real.sq_sqrt hx.le
  have he : Real.exp (-1 / (4 * x)) ^ 2 = Real.exp (-(1 / 2 : ℝ) / x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hid : (Real.exp (-1 / (4 * x)) ^ 2 *
      ((2 / (x * Real.sqrt x)) * (1 + 18 / x) + 6 * x * Real.sqrt x / ε)) / x ^ 2 =
      2 * (Real.exp (-(1 / 2 : ℝ) / x) / (x ^ 3 * Real.sqrt x)) +
      36 * (Real.exp (-(1 / 2 : ℝ) / x) / (x ^ 4 * Real.sqrt x)) +
      6 * Real.exp (-(1 / 2 : ℝ) / x) / (Real.sqrt x * ε) := by
    rw [he]
    field_simp
    rw [hsq]
    ring
  rw [hid]
  have h3 := pure_gaussian_half_power_bound hx hxR 3 (by norm_num)
  have h4 := pure_gaussian_half_power_bound hx hxR 4 (by norm_num)
  have hm := (cutoff_width_mixed_tail_bound hx hxR hε hwidth).trans_lt
    (show 4000 * Real.exp (-(9 / 20 : ℝ) / x) / x <
      4000 * (250 / (10 : ℝ) ^ 48) by
      have h := mul_lt_mul_of_pos_left (mixed_gaussian_inverse_power_bound hx hxR)
        (by norm_num : (0 : ℝ) < 4000)
      convert! h using 1 <;> ring)
  calc
    _ < 2 * (16 * (250 : ℝ) ^ 3 / (10 : ℝ) ^ 53) +
      36 * (16 * (250 : ℝ) ^ 4 / (10 : ℝ) ^ 53) +
      4000 * (250 / (10 : ℝ) ^ 48) := by linarith
    _ < _ := by norm_num

/-- The cutoff high-frequency square-root energy has the strong 10^(-20) ratio. -/
theorem sqrt_cutoff_gaussian_energy_lt {x ε : ℝ} (hx : 0 < x) (hxR : x ≤ 1 / 250)
    (hε : 0 < ε)
    (hwidth : 1 / ε ≤ 100000 / (150 * Real.sqrt (2 * x)) *
      Real.exp (1 / Real.sqrt (2 * x))) :
    Real.sqrt (Real.exp (-1 / (4 * x)) ^ 2 *
      ((2 / (x * Real.sqrt x)) * (1 + 18 / x) + 6 * x * Real.sqrt x / ε)) <
      x / (10 : ℝ) ^ 20 := by
  apply (Real.sqrt_lt' (by positivity)).mpr
  have h := (div_lt_iff₀ (sq_pos_of_pos hx)).mp
    (cutoff_gaussian_energy_div_sq_lt hx hxR hε hwidth)
  convert! h using 1 <;> norm_num <;> ring

end LpSelfSimilar.Analysis
