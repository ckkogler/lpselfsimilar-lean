module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic

@[expose] public section

/-!
# The exact quadratic approximation to log cosine on [-1,1]

Differentiating v^3/3-sin(v)+v*cos(v) gives v*(v-sin(v)), which is nonnegative
for v>=0. Since cos(v)>=1/2 on [-1,1], division proves the tangent remainder
bound 2*v^3/3. Integrating this derivative bound proves the log-cosine remainder
bound v^4/6, including the endpoints. No power-series estimate is assumed.
-/

open Set

namespace LpSelfSimilar.Analysis

/-- The cosine denominator is uniformly positive on the closed unit interval. -/
theorem half_le_cos_of_abs_le_one {v : ℝ} (hv : |v| ≤ 1) :
    (1 / 2 : ℝ) ≤ Real.cos v := by
  have hsq : v ^ 2 ≤ 1 := by nlinarith [sq_abs v, abs_nonneg v]
  nlinarith [Real.one_sub_sq_div_two_le_cos (x := v)]

/-- The numerator of tan(v)-v is bounded by v^3/3 on the nonnegative half-line. -/
theorem sin_sub_mul_cos_le_cube_div_three {v : ℝ} (hv : 0 ≤ v) :
    Real.sin v - v * Real.cos v ≤ v ^ 3 / 3 := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 3 / 3 - Real.sin y + y * Real.cos y)
      (x * (x - Real.sin x)) x := by
    convert! ((((hasDerivAt_id x).pow 3).div_const 3).sub (Real.hasDerivAt_sin x)).add
      ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)) using 1 <;> simp only [id_eq] <;> ring
  have hm : MonotoneOn (fun y : ℝ => y ^ 3 / 3 - Real.sin y + y * Real.cos y) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · fun_prop
    · intro x hx
      exact (hd x).hasDerivWithinAt
    · intro x hx
      have hx0 : 0 ≤ x := interior_subset hx
      exact mul_nonneg hx0 (sub_nonneg.mpr (Real.sin_le hx0))
  have h := hm (show (0 : ℝ) ∈ Ici 0 from by simp) hv hv
  simp only [zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_div, Real.sin_zero,
    sub_zero, zero_mul, add_zero] at h
  linarith

/-- The tangent remainder has the exact cubic bound used in the Gaussian comparison. -/
theorem tan_sub_self_bounds_of_nonneg_le_one {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ Real.tan v - v ∧ Real.tan v - v ≤ (2 / 3 : ℝ) * v ^ 3 := by
  have hc := half_le_cos_of_abs_le_one (v := v) (by simpa only [abs_of_nonneg hv0] using hv1)
  have hcp : 0 < Real.cos v := by linarith
  refine ⟨sub_nonneg.mpr (Real.le_tan hv0 (by linarith [Real.pi_gt_d2])), ?_⟩
  have ht : Real.tan v - v = (Real.sin v - v * Real.cos v) / Real.cos v := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  rw [ht]
  apply (div_le_iff₀ hcp).mpr
  have h := sin_sub_mul_cos_le_cube_div_three hv0
  have hp := mul_nonneg (pow_nonneg hv0 3) (sub_nonneg.mpr hc)
  nlinarith

/-- The actual error in the quadratic approximation of log cosine. -/
noncomputable def logCosineRemainder (v : ℝ) : ℝ := -Real.log (Real.cos v) - v ^ 2 / 2

/-- Its actual derivative is the tangent remainder wherever the cosine is nonzero. -/
theorem hasDerivAt_logCosineRemainder {v : ℝ} (hv : Real.cos v ≠ 0) :
    HasDerivAt logCosineRemainder (Real.tan v - v) v := by
  unfold logCosineRemainder
  convert! (((Real.hasDerivAt_cos v).log hv).neg).sub
    (((hasDerivAt_id v).pow 2).div_const 2) using 1 <;>
    simp only [id_eq, Real.tan_eq_sin_div_cos] <;> ring

/-- Integrating the tangent bound gives the exact quartic remainder for 0<=v<=1. -/
theorem logCosineRemainder_bounds_of_nonneg_le_one {v : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    0 ≤ logCosineRemainder v ∧ logCosineRemainder v ≤ v ^ 4 / 6 := by
  have hc (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : Real.cos x ≠ 0 := by
    have h := half_le_cos_of_abs_le_one (v := x) (by simpa only [abs_of_nonneg hx.1] using hx.2)
    linarith
  have hcont : ContinuousOn logCosineRemainder (Icc (0 : ℝ) 1) :=
    fun x hx => (hasDerivAt_logCosineRemainder (hc x hx)).continuousAt.continuousWithinAt
  have hm : MonotoneOn logCosineRemainder (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont
    · intro x hx
      exact (hasDerivAt_logCosineRemainder (hc x (interior_subset hx))).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
      exact (tan_sub_self_bounds_of_nonneg_le_one hx'.1 hx'.2).1
  have hm' : MonotoneOn (fun x : ℝ => x ^ 4 / 6 - logCosineRemainder x) (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      ((continuous_pow 4).continuousOn.div_const 6 |>.sub hcont)
      (f' := fun x => (2 / 3 : ℝ) * x ^ 3 - (Real.tan x - x))
    · intro x hx
      have hd := (((hasDerivAt_id x).pow 4).div_const 6).sub
        (hasDerivAt_logCosineRemainder (hc x (interior_subset hx)))
      convert! hd.hasDerivWithinAt using 1 <;> simp only [id_eq] <;> ring
    · intro x hx
      have hx' : x ∈ Icc (0 : ℝ) 1 := interior_subset hx
      exact sub_nonneg.mpr (tan_sub_self_bounds_of_nonneg_le_one hx'.1 hx'.2).2
  have h0 : logCosineRemainder 0 = 0 := by simp [logCosineRemainder]
  have h := hm (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, by norm_num⟩) ⟨hv0, hv1⟩ hv0
  have h' := hm' (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, by norm_num⟩) ⟨hv0, hv1⟩ hv0
  rw [h0] at h
  simp only [zero_pow (by norm_num : (4 : ℕ) ≠ 0), zero_div, h0, sub_zero] at h'
  exact ⟨h, by linarith⟩

/-- The remainder is even, since the cosine and the quadratic term are even. -/
theorem logCosineRemainder_neg (v : ℝ) : logCosineRemainder (-v) = logCosineRemainder v := by
  simp [logCosineRemainder]

/-- The full closed-interval log-cosine error estimate, with exact constant one sixth. -/
theorem logCosineRemainder_bounds {v : ℝ} (hv : |v| ≤ 1) :
    0 ≤ logCosineRemainder v ∧ logCosineRemainder v ≤ v ^ 4 / 6 := by
  by_cases h0 : 0 ≤ v
  · exact logCosineRemainder_bounds_of_nonneg_le_one h0 (by simpa [abs_of_nonneg h0] using hv)
  · have hv0 : 0 ≤ -v := by linarith
    have hv1 : -v ≤ 1 := by simpa [abs_of_neg (lt_of_not_ge h0)] using hv
    simpa only [logCosineRemainder_neg, show (-v) ^ 4 = v ^ 4 by ring] using
      logCosineRemainder_bounds_of_nonneg_le_one hv0 hv1

/-- The actual derivative's absolute value is controlled by two thirds of the absolute cube. -/
theorem abs_tan_sub_self_le_two_thirds_abs_cube {v : ℝ} (hv : |v| ≤ 1) :
    |Real.tan v - v| ≤ (2 / 3 : ℝ) * |v| ^ 3 := by
  by_cases h0 : 0 ≤ v
  · have h := tan_sub_self_bounds_of_nonneg_le_one h0 (by simpa [abs_of_nonneg h0] using hv)
    simpa only [abs_of_nonneg h.1, abs_of_nonneg h0] using h.2
  · have hv0 : 0 ≤ -v := by linarith
    have hv1 : -v ≤ 1 := by simpa [abs_of_neg (lt_of_not_ge h0)] using hv
    have h := tan_sub_self_bounds_of_nonneg_le_one hv0 hv1
    rw [Real.tan_neg] at h
    have ht : Real.tan v - v ≤ 0 := by linarith [h.1]
    rw [abs_of_nonpos ht, abs_of_neg (lt_of_not_ge h0)]
    linarith [h.2]

end LpSelfSimilar.Analysis
