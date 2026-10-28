module

public import LpSelfSimilar.Algebraic.MahlerMeasure

@[expose] public section

/-!
The canonical algebraic complexity in the revised Section 3.

The degree and Mahler measure come from the actual rational minimal polynomial,
not chosen bounds. Positivity of its logarithm for parameters in (0,1) justifies
every division. The lower bound three works also in degree one and at the
transition where the logarithm equals one.
-/

namespace LpSelfSimilar.Algebraic

/-- The exact degree/Mahler complexity B of the paper, using real division and
the natural logarithm. -/
noncomputable def complexity (x : ℝ) : ℝ :=
  (1 + (algebraicDegree x : ℝ) + Real.log (mahlerMeasure x)) /
    min 1 (Real.log (mahlerMeasure x))

lemma complexity_denominator_pos {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : 0 < min 1 (Real.log (mahlerMeasure x)) :=
  lt_min zero_lt_one (log_mahlerMeasure_pos hx hx0 hx1)

lemma complexity_pos {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : 0 < complexity x := by
  have hL := log_mahlerMeasure_pos hx hx0 hx1
  exact div_pos (by positivity) (complexity_denominator_pos hx hx0 hx1)

/-- The first numerical bound in the algebraic arithmetic lemma. -/
lemma three_le_complexity {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : 3 ≤ complexity x := by
  have hd : (1 : ℝ) ≤ algebraicDegree x := by exact_mod_cast algebraicDegree_pos hx
  apply (le_div_iff₀ (complexity_denominator_pos hx hx0 hx1)).mpr
  have h1 := min_le_left (1 : ℝ) (Real.log (mahlerMeasure x))
  have hL := min_le_right (1 : ℝ) (Real.log (mahlerMeasure x))
  linarith

lemma log_mahlerMeasure_le_complexity {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : Real.log (mahlerMeasure x) ≤ complexity x := by
  have hL := log_mahlerMeasure_pos hx hx0 hx1
  apply (le_div_iff₀ (complexity_denominator_pos hx hx0 hx1)).mpr
  have hm := mul_le_mul_of_nonneg_left
    (min_le_left (1 : ℝ) (Real.log (mahlerMeasure x))) hL.le
  have hd : (0 : ℝ) ≤ algebraicDegree x := Nat.cast_nonneg _
  linarith

lemma degree_le_complexity {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : (algebraicDegree x : ℝ) ≤ complexity x := by
  have hL := log_mahlerMeasure_pos hx hx0 hx1
  apply (le_div_iff₀ (complexity_denominator_pos hx hx0 hx1)).mpr
  have hm := mul_le_mul_of_nonneg_left
    (min_le_left (1 : ℝ) (Real.log (mahlerMeasure x)))
    (Nat.cast_nonneg (α := ℝ) (algebraicDegree x))
  linarith

lemma degree_add_log_mahlerMeasure_le_complexity {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (algebraicDegree x : ℝ) + Real.log (mahlerMeasure x) ≤ complexity x := by
  have hL := log_mahlerMeasure_pos hx hx0 hx1
  apply (le_div_iff₀ (complexity_denominator_pos hx hx0 hx1)).mpr
  have hm := mul_le_mul_of_nonneg_left
    (min_le_left (1 : ℝ) (Real.log (mahlerMeasure x)))
    (show 0 ≤ (algebraicDegree x : ℝ) + Real.log (mahlerMeasure x) by positivity)
  linarith

lemma inv_complexity (x : ℝ) :
    (complexity x)⁻¹ = min 1 (Real.log (mahlerMeasure x)) /
      (1 + (algebraicDegree x : ℝ) + Real.log (mahlerMeasure x)) := by
  simp only [complexity, inv_div]

end LpSelfSimilar.Algebraic
