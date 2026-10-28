module

public import LpSelfSimilar.Algebraic.ReflectedPolynomialNormalization
public import LpSelfSimilar.Algebraic.DegreePowers

@[expose] public section

/-!
# Exact primitive minimal polynomials under squaring

Let P and Q be the canonical primitive, positive-leading integer minimal
polynomials of x and x squared. For even P, its even-coefficient contraction
and integer minimal-polynomial divisibility give P(X)=Q(X squared). Otherwise
P and its reflection are relatively prime. Comparing their product with the
square expansion of Q gives equality up to a unit; positive normalization fixes
that unit to exactly (-1)^degree(P). No common-root or distinct-square assertion
is assumed in this proof.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- The canonical minimal polynomial divides the square expansion of the squared parameter's polynomial. -/
theorem integerMinimalPolynomial_dvd_square_expansion {x : ℝ} (hx : IsAlgebraic ℚ x) :
    integerMinimalPolynomial x ∣ expand ℤ 2 (integerMinimalPolynomial (x ^ 2)) := by
  apply (integerMinimalPolynomial_dvd_iff hx).mpr
  rw [expand_aeval, integerMinimalPolynomial_aeval]

/-- Every even integer polynomial vanishing at x is divisible by the square expansion of Q. -/
theorem square_minimal_expansion_dvd_even_polynomial {x : ℝ} (hx : IsAlgebraic ℚ x)
    {p : ℤ[X]} (heven : p.comp (-X) = p) (hroot : aeval x p = 0) :
    expand ℤ 2 (integerMinimalPolynomial (x ^ 2)) ∣ p := by
  have he := polynomial_expand_contract_two heven
  have hr : aeval (x ^ 2) (contract 2 p) = 0 := by
    have h := congrArg (aeval x) he
    rwa [expand_aeval, hroot] at h
  obtain ⟨t, ht⟩ := (integerMinimalPolynomial_dvd_iff (isAlgebraic_pow hx 2)).mpr hr
  refine ⟨expand ℤ 2 t, ?_⟩
  rw [← map_mul, ← ht, he]

/-- The square expansion of the canonical polynomial retains its positive normalization. -/
theorem normalize_integerMinimalPolynomial_square_expansion {x : ℝ} (hx : IsAlgebraic ℚ x) :
    normalize (expand ℤ 2 (integerMinimalPolynomial (x ^ 2))) =
      expand ℤ 2 (integerMinimalPolynomial (x ^ 2)) := by
  apply normalize_eq_self_of_leadingCoeff_nonneg
  rw [leadingCoeff_expand (by norm_num : 0 < (2 : ℕ))]
  exact (integerMinimalPolynomial_leadingCoeff_pos (isAlgebraic_pow hx 2)).le

/-- The exact even-case primitive minimal-polynomial formula. -/
theorem integerMinimalPolynomial_square_of_even {x : ℝ} (hx : IsAlgebraic ℚ x)
    (heven : (integerMinimalPolynomial x).comp (-X) = integerMinimalPolynomial x) :
    integerMinimalPolynomial x = (integerMinimalPolynomial (x ^ 2)).comp (X ^ 2) := by
  change integerMinimalPolynomial x = expand ℤ 2 (integerMinimalPolynomial (x ^ 2))
  exact (associated_of_dvd_dvd (integerMinimalPolynomial_dvd_square_expansion hx)
    (square_minimal_expansion_dvd_even_polynomial hx heven (integerMinimalPolynomial_aeval x))).eq_of_normalized
      (normalize_integerMinimalPolynomial x) (normalize_integerMinimalPolynomial_square_expansion hx)

/-- In the non-even case, the actual primitive polynomial and its reflection are relatively prime. -/
theorem integerMinimalPolynomial_isRelPrime_reflection {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : x ≠ 0)
    (hne : (integerMinimalPolynomial x).comp (-X) ≠ integerMinimalPolynomial x) :
    IsRelPrime (integerMinimalPolynomial x) ((integerMinimalPolynomial x).comp (-X)) :=
  (integerMinimalPolynomial_irreducible hx).isRelPrime_iff_not_dvd.mpr
    (polynomial_not_dvd_reflection (integerMinimalPolynomial_irreducible hx)
      (integerMinimalPolynomial_coeff_zero_ne_zero hx hx0) hne)

/-- The exact non-even formula, including the primitive scalar and leading sign. -/
theorem integerMinimalPolynomial_square_of_not_even {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : x ≠ 0)
    (hne : (integerMinimalPolynomial x).comp (-X) ≠ integerMinimalPolynomial x) :
    (integerMinimalPolynomial (x ^ 2)).comp (X ^ 2) =
      C ((-1 : ℤ) ^ algebraicDegree x) * integerMinimalPolynomial x *
        (integerMinimalPolynomial x).comp (-X) := by
  let p := integerMinimalPolynomial x
  let q := expand ℤ 2 (integerMinimalPolynomial (x ^ 2))
  have hp : p ∣ q := integerMinimalPolynomial_dvd_square_expansion hx
  have hn : p.comp (-X) ∣ q := by
    apply (dvd_comp_neg_X_iff p q).mp
    rw [polynomial_expand_two_reflection]
    exact hp
  have hprod : p * p.comp (-X) ∣ q :=
    (integerMinimalPolynomial_isRelPrime_reflection hx hx0 hne).mul_dvd hp hn
  have hq : q ∣ p * p.comp (-X) :=
    square_minimal_expansion_dvd_even_polynomial hx (polynomial_product_reflection p)
      (by simp only [map_mul, p, integerMinimalPolynomial_aeval, zero_mul])
  have he := ((signed_reflection_product_associated p).trans
    (associated_of_dvd_dvd hprod hq)).eq_of_normalized
      (normalize_signed_reflection_product p) (normalize_integerMinimalPolynomial_square_expansion hx)
  simpa only [p, q, expand_eq_comp_X_pow, integerMinimalPolynomial_natDegree, mul_assoc] using he.symm

end LpSelfSimilar.Algebraic
