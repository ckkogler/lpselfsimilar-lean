module

public import LpSelfSimilar.Analysis.ExponentialTailNumerics

@[expose] public section

/-!
# The numerical Gaussian tail energy margin

After division by the squared gap, the tail energy is bounded by the
half-integral powers 5/2 and 3/2. Exact endpoint comparisons prove a
squared ratio below 10^(-46), and hence the claimed square-root margin.
-/

namespace LpSelfSimilar.Analysis

/-- A simple majorant for the Gaussian boundary coefficient at the inverse-square-root endpoint. -/
theorem gaussian_tail_coefficient_le {x : ℝ} (hx : 0 < x) :
    Real.sqrt (1 / (2 * x)) / 2 + 3 / (4 * Real.sqrt (1 / (2 * x))) ≤
      1 / Real.sqrt x + 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have ht : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have ht2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have htlo : 1 ≤ Real.sqrt (2 : ℝ) := by nlinarith
  have hthi : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith
  have he : Real.sqrt (1 / (2 * x)) = 1 / (Real.sqrt (2 : ℝ) * Real.sqrt x) := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  rw [he]
  have h0 : 1 / (Real.sqrt (2 : ℝ) * Real.sqrt x) ≤ 1 / Real.sqrt x :=
    one_div_le_one_div_of_le hs (by nlinarith)
  have h1 : 1 / (1 / (Real.sqrt (2 : ℝ) * Real.sqrt x)) ≤ 2 * Real.sqrt x := by
    rw [one_div_one_div]
    exact mul_le_mul_of_nonneg_right hthi hs.le
  calc
    _ = (1 / (Real.sqrt (2 : ℝ) * Real.sqrt x)) / 2 +
      (3 / 4 : ℝ) * (1 / (1 / (Real.sqrt (2 : ℝ) * Real.sqrt x))) := by ring
    _ ≤ (1 / Real.sqrt x) / 2 + (3 / 4 : ℝ) * (2 * Real.sqrt x) :=
      add_le_add (div_le_div_of_nonneg_right h0 (by norm_num))
        (mul_le_mul_of_nonneg_left h1 (by norm_num))
    _ ≤ _ := by
      have hp : 0 ≤ 1 / Real.sqrt x := by positivity
      nlinarith

/-- The normalized Gaussian tail energy is strictly below the exact decimal margin. -/
theorem gaussian_tail_energy_div_sq_lt {x : ℝ} (hx : 0 < x) (hxR : x ≤ 1 / 250) :
    ((Real.sqrt (1 / (2 * x)) / 2 + 3 / (4 * Real.sqrt (1 / (2 * x)))) *
      Real.exp (-(1 / (2 * x)))) / x ^ 2 < 1 / (10 : ℝ) ^ 46 := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hsq := Real.sq_sqrt hx.le
  have he : -(1 / (2 * x)) = -(1 / 2 : ℝ) / x := by ring
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (gaussian_tail_coefficient_le hx)
      (Real.exp_nonneg (-(1 / (2 * x))))) (sq_nonneg x)
  have hid : ((1 / Real.sqrt x + 2 * Real.sqrt x) *
      Real.exp (-(1 / (2 * x)))) / x ^ 2 =
      Real.exp (-(1 / 2 : ℝ) / x) / (x ^ 2 * Real.sqrt x) +
        2 * (Real.exp (-(1 / 2 : ℝ) / x) / (x ^ 1 * Real.sqrt x)) := by
    rw [he]
    field_simp
    nlinarith
  rw [hid] at hm
  have h2 := pure_gaussian_half_power_bound hx hxR 2 (by norm_num)
  have h1 := pure_gaussian_half_power_bound hx hxR 1 (by norm_num)
  calc
    _ ≤ _ := hm
    _ < 16 * (250 : ℝ) ^ 2 / (10 : ℝ) ^ 53 +
        2 * (16 * (250 : ℝ) ^ 1 / (10 : ℝ) ^ 53) := by linarith
    _ < _ := by norm_num

/-- The Gaussian tail square-root ratio satisfies the strong 10^(-23) margin. -/
theorem sqrt_gaussian_tail_energy_lt {x : ℝ} (hx : 0 < x) (hxR : x ≤ 1 / 250) :
    Real.sqrt ((Real.sqrt (1 / (2 * x)) / 2 + 3 / (4 * Real.sqrt (1 / (2 * x)))) *
      Real.exp (-(1 / (2 * x)))) < x / (10 : ℝ) ^ 23 := by
  apply (Real.sqrt_lt' (by positivity)).mpr
  have h := (div_lt_iff₀ (sq_pos_of_pos hx)).mp (gaussian_tail_energy_div_sq_lt hx hxR)
  convert! h using 1 <;> norm_num <;> ring

end LpSelfSimilar.Analysis
