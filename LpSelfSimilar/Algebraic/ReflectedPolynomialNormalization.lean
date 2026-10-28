module

public import LpSelfSimilar.Algebraic.PolynomialParity

@[expose] public section

/-!
# The positive normalization of a polynomial times its reflection

Multiplying P(X)P(-X) by (-1)^degree(P) gives leading coefficient
leadingCoeff(P)^2. The multiplier is a unit, and Gauss's lemma proves the
result primitive whenever P is primitive. These facts remove every scalar
ambiguity from the non-even minimal-polynomial squaring formula.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- The sign-adjusted reflection product has exactly the squared leading coefficient. -/
theorem signed_reflection_product_leadingCoeff (p : ℤ[X]) :
    (C ((-1 : ℤ) ^ p.natDegree) * (p * p.comp (-X))).leadingCoeff = p.leadingCoeff ^ 2 := by
  rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_mul, comp_neg_X_leadingCoeff_eq]
  have hs : (-1 : ℤ) ^ p.natDegree * (-1) ^ p.natDegree = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((-1 : ℤ) ^ p.natDegree * (-1) ^ p.natDegree) * p.leadingCoeff ^ 2 := by ring
    _ = _ := by rw [hs, one_mul]

/-- The sign-adjusted reflection product is already positively normalized. -/
theorem normalize_signed_reflection_product (p : ℤ[X]) :
    normalize (C ((-1 : ℤ) ^ p.natDegree) * (p * p.comp (-X))) =
      C ((-1 : ℤ) ^ p.natDegree) * (p * p.comp (-X)) := by
  apply normalize_eq_self_of_leadingCoeff_nonneg
  rw [signed_reflection_product_leadingCoeff]
  exact sq_nonneg _

/-- The sign adjustment is an actual integer-polynomial unit. -/
theorem signed_reflection_product_associated (p : ℤ[X]) :
    Associated (C ((-1 : ℤ) ^ p.natDegree) * (p * p.comp (-X))) (p * p.comp (-X)) :=
  associated_unit_mul_left _ _ (isUnit_C.mpr (isUnit_neg_one.pow _))

/-- Gauss's lemma proves primitivity of the sign-adjusted reflection product. -/
theorem signed_reflection_product_isPrimitive {p : ℤ[X]} (hp : p.IsPrimitive) :
    (C ((-1 : ℤ) ^ p.natDegree) * (p * p.comp (-X))).IsPrimitive :=
  isPrimitive_of_dvd (hp.mul (isPrimitive_polynomial_reflection hp))
    (signed_reflection_product_associated p).dvd

end LpSelfSimilar.Algebraic
