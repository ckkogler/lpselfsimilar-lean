module

public import LpSelfSimilar.Algebraic.MinimalPolynomialSquaring
public import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

/-!
# Distinct squares of conjugates in the non-even case

Gauss descent transfers a hypothetical rational divisibility by the reflected
polynomial back to the primitive integer polynomial. Non-evenness and the
nonzero constant coefficient exclude it, so the rational polynomials are
coprime. Bezout then excludes opposite complex roots. Equality of complex
squares implies equality or opposition, proving the source's distinct-squares
claim without assuming it in the minimal-polynomial formula.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- The rational images of a non-even primitive irreducible polynomial and its reflection are coprime. -/
theorem rational_polynomial_coprime_reflection {p : ℤ[X]} (hp : p.IsPrimitive)
    (hi : Irreducible p) (hp0 : p.coeff 0 ≠ 0) (hne : p.comp (-X) ≠ p) :
    IsCoprime (p.map (algebraMap ℤ ℚ)) ((p.map (algebraMap ℤ ℚ)).comp (-X)) := by
  have hir : Irreducible (p.map (algebraMap ℤ ℚ)) :=
    (hp.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mp hi
  apply hir.coprime_iff_not_dvd.mpr
  intro hd
  apply polynomial_not_dvd_reflection hi hp0 hne
  apply (hp.dvd_iff_fraction_map_dvd_fraction_map (K := ℚ)).mpr
  simpa only [Polynomial.map_comp, Polynomial.map_neg, Polynomial.map_X] using hd

/-- A non-even primitive irreducible polynomial with nonzero constant coefficient has no opposite roots. -/
theorem integer_polynomial_no_opposite_roots {p : ℤ[X]} (hp : p.IsPrimitive)
    (hi : Irreducible p) (hp0 : p.coeff 0 ≠ 0) (hne : p.comp (-X) ≠ p)
    {z : ℂ} (hz : aeval z p = 0) : aeval (-z) p ≠ 0 := by
  have h := aeval_ne_zero_of_isCoprime (rational_polynomial_coprime_reflection hp hi hp0 hne) z
  have hz' : aeval z (p.map (algebraMap ℤ ℚ)) = 0 := by
    simpa only [aeval_map_algebraMap] using hz
  have hn := h.resolve_left (not_not_intro hz')
  simpa only [aeval_comp, map_neg, aeval_X, aeval_map_algebraMap] using hn

/-- Squaring is injective on the complex roots of a non-even primitive irreducible integer polynomial. -/
theorem square_injOn_integer_polynomial_roots {p : ℤ[X]} (hp : p.IsPrimitive)
    (hi : Irreducible p) (hp0 : p.coeff 0 ≠ 0) (hne : p.comp (-X) ≠ p) :
    Set.InjOn (fun z : ℂ => z ^ 2) {z : ℂ | aeval z p = 0} := by
  intro z hz w hw he
  change aeval z p = 0 at hz
  change aeval w p = 0 at hw
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · exact h
  · exact False.elim ((integer_polynomial_no_opposite_roots hp hi hp0 hne hw)
      (by simpa only [h] using hz))

/-- Distinct conjugates of a nonzero algebraic parameter have distinct squares in the non-even case. -/
theorem square_injOn_conjugates_of_not_even {x : ℝ} (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0)
    (hne : (integerMinimalPolynomial x).comp (-X) ≠ integerMinimalPolynomial x) :
    Set.InjOn (fun z : ℂ => z ^ 2) {z : ℂ | aeval z (integerMinimalPolynomial x) = 0} :=
  square_injOn_integer_polynomial_roots (integerMinimalPolynomial_isPrimitive hx)
    (integerMinimalPolynomial_irreducible hx) (integerMinimalPolynomial_coeff_zero_ne_zero hx hx0) hne

end LpSelfSimilar.Algebraic
