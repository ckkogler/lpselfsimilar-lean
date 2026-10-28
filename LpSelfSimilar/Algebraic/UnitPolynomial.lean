module

public import LpSelfSimilar.Algebraic.MinimalPolynomial
public import LpSelfSimilar.Algebraic.Units
public import Mathlib.Data.Int.Order.Units

@[expose] public section

/-!
The canonical integer polynomial of an algebraic unit is monic and has unit
constant coefficient. Both claims follow from polynomial divisibility: the
canonical polynomial divides the monic minimal polynomial of the integer, and
also the reversal of the monic minimal polynomial of its reciprocal. The latter
polynomial has constant coefficient one. This treats the actual canonical
normalization and supplies the determinant product used in the entropy proof.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

lemma integerMinimalPolynomial_monic_of_isIntegral {x : ℝ} (hx : IsIntegral ℤ x) :
    (integerMinimalPolynomial x).Monic := by
  have ha : IsAlgebraic ℚ x := (hx.tower_top (A := ℚ)).isAlgebraic
  obtain ⟨q, hq⟩ := (integerMinimalPolynomial_dvd_iff ha).mpr (minpoly.aeval ℤ x)
  have hd : (integerMinimalPolynomial x).leadingCoeff ∣ (1 : ℤ) := by
    refine ⟨q.leadingCoeff, ?_⟩
    rw [← leadingCoeff_mul, ← hq, (minpoly.monic hx).leadingCoeff]
  have habs := Int.isUnit_iff_abs_eq.mp (isUnit_of_dvd_one hd)
  rwa [abs_of_pos (integerMinimalPolynomial_leadingCoeff_pos ha)] at habs

lemma integerMinimalPolynomial_eq_minpoly_of_isIntegral {x : ℝ} (hx : IsIntegral ℤ x) :
    integerMinimalPolynomial x = minpoly ℤ x := by
  apply eq_of_monic_of_associated (integerMinimalPolynomial_monic_of_isIntegral hx)
    (minpoly.monic hx)
  have ha : IsAlgebraic ℚ x := (hx.tower_top (A := ℚ)).isAlgebraic
  apply (integerMinimalPolynomial_irreducible ha).associated_of_dvd
    (minpoly.irreducible hx)
  exact (integerMinimalPolynomial_dvd_iff ha).mpr (minpoly.aeval ℤ x)

/-- Reversing a monic polynomial for the integral inverse forces the canonical
constant coefficient to divide one. -/
lemma integerMinimalPolynomial_coeff_zero_isUnit {x : ℝ} (hx : IsAlgebraicUnit x) :
    IsUnit ((integerMinimalPolynomial x).coeff 0) := by
  have ha : IsAlgebraic ℚ x := (hx.2.1.tower_top (A := ℚ)).isAlgebraic
  let : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx.1)
  have hr : aeval x (minpoly ℤ x⁻¹).reverse = 0 := by
    have h := (eval₂_reverse_eq_zero_iff (algebraMap ℤ ℝ) x⁻¹ (minpoly ℤ x⁻¹)).mpr
      (minpoly.aeval ℤ x⁻¹)
    simpa only [invOf_eq_inv, inv_inv, ← aeval_def] using h
  obtain ⟨q, hq⟩ := (integerMinimalPolynomial_dvd_iff ha).mpr hr
  apply isUnit_of_dvd_one
  refine ⟨q.coeff 0, ?_⟩
  rw [← mul_coeff_zero, ← hq, coeff_zero_reverse, (minpoly.monic hx.2.2).leadingCoeff]

lemma integerMinimalPolynomial_coeff_zero_abs_eq_one {x : ℝ} (hx : IsAlgebraicUnit x) :
    |(integerMinimalPolynomial x).coeff 0| = 1 :=
  Int.isUnit_iff_abs_eq.mp (integerMinimalPolynomial_coeff_zero_isUnit hx)

end LpSelfSimilar.Algebraic
