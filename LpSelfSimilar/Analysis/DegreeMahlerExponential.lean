module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Conversion from degree/Mahler separation to an exponential scale.

This scalar estimate is independent of algebraic representations. Positivity
justifies the logarithms; the degree and logarithmic Mahler costs are each
bounded by the word length, with no unspecified constant.
-/

namespace LpSelfSimilar

lemma degree_mahler_denominator_le_exp {d n l : ℕ} (hn : n < l)
    {M B : ℝ} (hM : 1 ≤ M) (hB : (d : ℝ) + Real.log M ≤ B) :
    ((n : ℝ) + 1) ^ (d - 1) * M ^ n ≤ Real.exp (B * l) := by
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  have hnr : (n : ℝ) ≤ l := by exact_mod_cast hn.le
  have hdr : ((d - 1 : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d 1
  have hlogn : Real.log ((n : ℝ) + 1) ≤ l := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)
    linarith
  have hfirst : ((d - 1 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) ≤ (d : ℝ) * l :=
    (mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hdr (Nat.cast_nonneg _))
  have hsecond : (n : ℝ) * Real.log M ≤ (l : ℝ) * Real.log M :=
    mul_le_mul_of_nonneg_right hnr hlogM
  have hlast := mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg (α := ℝ) l)
  rw [← Real.exp_log (by positivity : 0 < ((n : ℝ) + 1) ^ (d - 1) * M ^ n)]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  nlinarith

end LpSelfSimilar
