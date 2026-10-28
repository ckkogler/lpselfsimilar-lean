module

public import LpSelfSimilar.Algebraic.Complexity
public import LpSelfSimilar.Analysis.PolynomialMahlerBounds

@[expose] public section

/-!
The logarithmic gap estimate in the algebraic arithmetic lemma.

The canonical integer minimal polynomial does not vanish at one unless the
parameter equals one. Its nonzero integer value has absolute value at least one.
Factoring out the actual real root and using the Mahler evaluation bound yields
1 <= (1-x) 2^(degree-1) M. Taking natural logarithms gives the exact bound by B.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- The integer evaluation and the distinguished real root give the paper's
multiplicative estimate before logarithms are taken. -/
theorem one_le_gap_mul_degree_mahler {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    1 ≤ (1 - x) * 2 ^ (algebraicDegree x - 1) * mahlerMeasure x := by
  let p := (integerMinimalPolynomial x).map (Int.castRingHom ℂ)
  have hp : p ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.castRingHom ℂ).injective_int).mpr
      (integerMinimalPolynomial_ne_zero hx)
  have hz : p.IsRoot (x : ℂ) := by
    change ((integerMinimalPolynomial x).map (algebraMap ℤ ℂ)).eval (x : ℂ) = 0
    rw [eval_map_algebraMap]
    exact integerMinimalPolynomial_complex_aeval x
  have he : p.eval 1 = (((integerMinimalPolynomial x).eval 1 : ℤ) : ℂ) := by
    change ((integerMinimalPolynomial x).map (algebraMap ℤ ℂ)).eval 1 = _
    rw [eval_map_algebraMap]
    have h := aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (1 : ℤ)
      (integerMinimalPolynomial x)
    simpa using h
  have hlow : (1 : ℝ) ≤ ‖p.eval 1‖ := by
    rw [he, Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (integerMinimalPolynomial_eval_one_ne_zero hx hx1.ne)
  have hxnorm : ‖(x : ℂ)‖ ≤ 1 := by simpa [abs_of_pos hx0] using hx1.le
  have hbound := polynomial_norm_eval_one_le_of_root hp hz hxnorm
  have hdeg : p.natDegree = algebraicDegree x := by
    rw [natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int,
      integerMinimalPolynomial_natDegree]
  have hnorm : ‖(1 : ℂ) - (x : ℂ)‖ = 1 - x := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hx1)]
  rw [hdeg, hnorm] at hbound
  exact hlow.trans hbound

/-- The fourth assertion of (3.8), for every positive contracting algebraic real. -/
theorem log_inverse_gap_le_complexity {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    Real.log (1 / (1 - x)) ≤ complexity x := by
  have hgap := sub_pos.mpr hx1
  have hM : 0 < mahlerMeasure x := (one_lt_mahlerMeasure hx hx0 hx1).trans' zero_lt_one
  have hinv : 1 / (1 - x) ≤ 2 ^ (algebraicDegree x - 1) * mahlerMeasure x := by
    apply (div_le_iff₀ hgap).mpr
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      one_le_gap_mul_degree_mahler hx hx0 hx1
  have hlog := Real.log_le_log (by positivity : 0 < 1 / (1 - x)) hinv
  rw [Real.log_mul (by positivity) hM.ne', Real.log_pow] at hlog
  have hd : ((algebraicDegree x - 1 : ℕ) : ℝ) ≤ algebraicDegree x := by
    exact_mod_cast Nat.sub_le (algebraicDegree x) 1
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hnum : ((algebraicDegree x - 1 : ℕ) : ℝ) * Real.log 2 ≤ algebraicDegree x := by
    calc
      _ ≤ ((algebraicDegree x - 1 : ℕ) : ℝ) * 1 := by gcongr
      _ ≤ algebraicDegree x := by simpa using hd
  have hsum : ((algebraicDegree x - 1 : ℕ) : ℝ) * Real.log 2 +
      Real.log (mahlerMeasure x) ≤ (algebraicDegree x : ℝ) +
      Real.log (mahlerMeasure x) := by linarith
  exact hlog.trans (hsum.trans (degree_add_log_mahlerMeasure_le_complexity hx hx0 hx1))

end LpSelfSimilar.Algebraic
