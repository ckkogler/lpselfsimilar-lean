module

public import LpSelfSimilar.Algebraic.Complexity
public import LpSelfSimilar.Rational.Complexity
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

/-!
Identification of the canonical algebraic invariants at rational parameters.

For a reduced nonnegative fraction a/b with b positive, the canonical primitive
integer polynomial is b X - a and the degree is one. If a < b its Mahler measure
is exactly b. Consequently the algebraic complexity agrees with the rational
complexity already used in the preserved exponent-fifty formalization. This is
an equality of the actual definitions, with coprimality and normalization proved.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

lemma rational_linear_isPrimitive {a b : ℕ} (hab : a.Coprime b) :
    (C (b : ℤ) * X - C (a : ℤ)).IsPrimitive := by
  intro r hr
  have h0 := ((C_dvd_iff_dvd_coeff _ _).mp hr) 0
  have h1 := ((C_dvd_iff_dvd_coeff _ _).mp hr) 1
  have ha : r ∣ (a : ℤ) := by simpa using h0
  have hb : r ∣ (b : ℤ) := by simpa using h1
  exact hab.isCoprime.isUnit_of_dvd' ha hb

lemma minpoly_rat_div (a b : ℕ) :
    minpoly ℚ ((a : ℝ) / b) = X - C ((a : ℚ) / b) := by
  have hcast : algebraMap ℚ ℝ ((a : ℚ) / b) = (a : ℝ) / b := by simp
  rw [← hcast, minpoly.eq_X_sub_C]

lemma algebraicDegree_rat_div (a b : ℕ) :
    algebraicDegree ((a : ℝ) / b) = 1 := by
  rw [algebraicDegree, minpoly_rat_div, natDegree_X_sub_C]

/-- Reduced fractions have precisely the expected canonical integer polynomial. -/
theorem integerMinimalPolynomial_rat_div {a b : ℕ} (hb : 0 < b)
    (hab : a.Coprime b) :
    integerMinimalPolynomial ((a : ℝ) / b) = C (b : ℤ) * X - C (a : ℤ) := by
  unfold integerMinimalPolynomial
  apply Eq.symm
  apply eq_primitiveRepresentative_of_associated
    (by rw [minpoly_rat_div]; exact X_sub_C_ne_zero _)
    (rational_linear_isPrimitive hab)
  · apply normalize_eq_self_of_leadingCoeff_nonneg
    have hdeg : (C (a : ℤ)).degree < (C (b : ℤ) * X).degree :=
      degree_C_lt_degree_C_mul_X (by exact_mod_cast hb.ne')
    rw [leadingCoeff_sub_of_degree_lt hdeg, leadingCoeff_mul, leadingCoeff_C,
      leadingCoeff_X, mul_one]
    positivity
  · rw [minpoly_rat_div]
    have hbe : (b : ℚ) ≠ 0 := by positivity
    have he : (C (b : ℤ) * X - C (a : ℤ)).map (algebraMap ℤ ℚ) =
        C (b : ℚ) * (X - C ((a : ℚ) / b)) := by
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X]
      change C (b : ℚ) * X - C (a : ℚ) = C (b : ℚ) * (X - C ((a : ℚ) / b))
      rw [mul_sub, ← C_mul, mul_div_cancel₀ _ hbe]
    rw [he]
    exact associated_unit_mul_left _ _ (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbe))

/-- Below one, the denominator is the Mahler measure, not merely an upper bound. -/
theorem mahlerMeasure_rat_div {a b : ℕ} (hb : 0 < b) (hab : a.Coprime b)
    (hlt : a < b) : mahlerMeasure ((a : ℝ) / b) = (b : ℝ) := by
  rw [mahlerMeasure, integerMinimalPolynomial_rat_div hb hab]
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Int.coe_castRingHom, Int.cast_natCast]
  rw [sub_eq_add_neg, ← map_neg C (a : ℂ),
    Polynomial.mahlerMeasure_C_mul_X_add_C (by exact_mod_cast hb.ne')]
  simp only [norm_neg, Complex.norm_natCast]
  exact max_eq_left (by exact_mod_cast hlt.le)

theorem complexity_rat_div {a b : ℕ} (hb : 0 < b) (hab : a.Coprime b)
    (hlt : a < b) : complexity ((a : ℝ) / b) = Rational.complexity b := by
  rw [complexity, algebraicDegree_rat_div, mahlerMeasure_rat_div hb hab hlt]
  norm_num [Rational.complexity]

end LpSelfSimilar.Algebraic
