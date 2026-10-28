module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section

/-!
# The quintic cutoff transition

The transition from one to zero has its first two derivatives zero at both
endpoints. Explicit derivative formulas and rational uniform bounds prepare the
piecewise Fourier cutoff; these are statements about ordinary polynomials.
-/

open Set MeasureTheory

namespace LpSelfSimilar.Analysis

/-- The quintic transition from one to zero. -/
noncomputable def quinticTransition (u : ℝ) : ℝ := 1 - 10 * u ^ 3 + 15 * u ^ 4 - 6 * u ^ 5

/-- First derivative of the quintic transition, in factored form. -/
noncomputable def quinticTransitionSlope (u : ℝ) : ℝ := -30 * u ^ 2 * (1 - u) ^ 2

/-- Second derivative of the quintic transition. -/
noncomputable def quinticTransitionCurvature (u : ℝ) : ℝ := -60 * u + 180 * u ^ 2 - 120 * u ^ 3

/-- Third derivative of the quintic transition. -/
noncomputable def quinticTransitionThird (u : ℝ) : ℝ := -60 + 360 * u - 360 * u ^ 2

/-- The factored slope is the actual derivative of the transition. -/
theorem hasDerivAt_quinticTransition (u : ℝ) :
    HasDerivAt quinticTransition (quinticTransitionSlope u) u := by
  convert! ((((hasDerivAt_const u (1 : ℝ)).sub (((hasDerivAt_id u).pow 3).const_mul 10)).add
    (((hasDerivAt_id u).pow 4).const_mul 15)).sub
    (((hasDerivAt_id u).pow 5).const_mul 6)) using 1 <;>
    simp only [quinticTransition, quinticTransitionSlope, id_eq, Pi.pow_apply] <;> ring

/-- The curvature is the actual derivative of the slope. -/
theorem hasDerivAt_quinticTransitionSlope (u : ℝ) :
    HasDerivAt quinticTransitionSlope (quinticTransitionCurvature u) u := by
  convert! ((((hasDerivAt_id u).pow 2).const_mul (-30)).mul
    (((hasDerivAt_id u).const_sub 1).pow 2)) using 1 <;>
    simp only [quinticTransitionSlope, quinticTransitionCurvature, id_eq, Pi.pow_apply] <;> ring

/-- The third polynomial is the actual derivative of the curvature. -/
theorem hasDerivAt_quinticTransitionCurvature (u : ℝ) :
    HasDerivAt quinticTransitionCurvature (quinticTransitionThird u) u := by
  convert! ((((hasDerivAt_id u).const_mul (-60)).add
    (((hasDerivAt_id u).pow 2).const_mul 180)).sub
    (((hasDerivAt_id u).pow 3).const_mul 120)) using 1 <;>
    simp only [quinticTransitionCurvature, quinticTransitionThird, id_eq, Pi.pow_apply] <;> ring

/-- Endpoint values and both vanishing derivatives of the transition. -/
theorem quinticTransition_endpoints :
    quinticTransition 0 = 1 ∧ quinticTransition 1 = 0 ∧
    quinticTransitionSlope 0 = 0 ∧ quinticTransitionSlope 1 = 0 ∧
    quinticTransitionCurvature 0 = 0 ∧ quinticTransitionCurvature 1 = 0 := by
  norm_num [quinticTransition, quinticTransitionSlope, quinticTransitionCurvature]

/-- The transition slope is nonpositive everywhere. -/
theorem quinticTransitionSlope_nonpos (u : ℝ) : quinticTransitionSlope u ≤ 0 := by
  unfold quinticTransitionSlope
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)

/-- The transition takes values between zero and one throughout the unit interval. -/
theorem quinticTransition_mem_Icc {u : ℝ} (hu : u ∈ Icc 0 1) :
    quinticTransition u ∈ Icc 0 1 := by
  have h0 := hu.1
  have h1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have ha : 0 ≤ (1 - u) ^ 3 * (1 + 3 * u + 6 * u ^ 2) := by positivity
  have hb : 0 ≤ u ^ 3 * (1 + 3 * (1 - u) + 6 * (1 - u) ^ 2) := by positivity
  constructor <;> unfold quinticTransition <;> nlinarith

/-- The largest absolute slope is at most fifteen eighths. -/
theorem abs_quinticTransitionSlope_le {u : ℝ} (hu : u ∈ Icc 0 1) :
    |quinticTransitionSlope u| ≤ 15 / 8 := by
  have h0 : 0 ≤ u * (1 - u) := mul_nonneg hu.1 (sub_nonneg.mpr hu.2)
  have h1 : u * (1 - u) ≤ 1 / 4 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have hs := pow_le_pow_left₀ h0 h1 2
  rw [abs_of_nonpos (quinticTransitionSlope_nonpos u)]
  unfold quinticTransitionSlope
  nlinarith

/-- A rational majorant for the centered cubic shape used in the second derivative. -/
theorem abs_sub_cube_le_two_fifths {t : ℝ} (ht : |t| ≤ 1) :
    |t - t ^ 3| ≤ 2 / 5 := by
  have hr0 : 0 ≤ |t| := abs_nonneg t
  have hr : |t| - |t| ^ 3 ≤ 2 / 5 := by
    by_cases h : |t| ≤ 2 / 5
    · nlinarith [pow_nonneg hr0 3]
    · have hs : 0 ≤ (|t| - 3 / 5) ^ 2 * (|t| + 6 / 5) := by positivity
      nlinarith
  have hs : t ^ 2 ≤ 1 := by nlinarith [sq_abs t]
  calc
    |t - t ^ 3| = |t| * (1 - t ^ 2) := by
      rw [show t - t ^ 3 = t * (1 - t ^ 2) by ring, abs_mul,
        abs_of_nonneg (sub_nonneg.mpr hs)]
    _ = |t| - |t| ^ 3 := by rw [← sq_abs t]; ring
    _ ≤ _ := hr

/-- The transition curvature has the rational bound six on the unit interval. -/
theorem abs_quinticTransitionCurvature_le {u : ℝ} (hu : u ∈ Icc 0 1) :
    |quinticTransitionCurvature u| ≤ 6 := by
  have ht : |2 * u - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hb := mul_le_mul_of_nonneg_left (abs_sub_cube_le_two_fifths ht)
    (show (0 : ℝ) ≤ 15 by norm_num)
  have he : quinticTransitionCurvature u = 15 * ((2 * u - 1) - (2 * u - 1) ^ 3) := by
    unfold quinticTransitionCurvature
    ring
  rw [he, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 15)]
  linarith

/-- The third derivative has absolute value at most sixty on the unit interval. -/
theorem abs_quinticTransitionThird_le {u : ℝ} (hu : u ∈ Icc 0 1) :
    |quinticTransitionThird u| ≤ 60 := by
  have h0 := mul_nonneg hu.1 (sub_nonneg.mpr hu.2)
  rw [abs_le]
  unfold quinticTransitionThird
  constructor <;> nlinarith [sq_nonneg (u - 1 / 2)]

end LpSelfSimilar.Analysis
