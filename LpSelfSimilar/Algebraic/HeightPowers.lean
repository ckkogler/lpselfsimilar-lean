module

public import LpSelfSimilar.Algebraic.RootPowerFactorization
public import LpSelfSimilar.Algebraic.MahlerPowers

@[expose] public section

/-!
The exact normalized-height identity under positive integer powers.

The root-power resultant of the canonical primitive integer minimal polynomial
is a power of the canonical polynomial of x^k. Its degree determines the
multiplicity. Its Mahler measure, computed independently by the complex root
product, is M(x)^k. Taking logarithms and dividing by the actual algebraic
degrees proves log M(x^k)/d(x^k) = k log M(x)/d(x). No integrality or monicity
assumption is imposed on x, and all denominators are proved nonzero.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- Canonical integer normalization fixes the unit in the repeated-factor
identity; the degree equation fixes the multiplicity. -/
theorem integerMinimalPolynomial_rootPowers_eq_pow {x : ℝ}
    (hx : IsAlgebraic ℚ x) {k : ℕ} (hk : 0 < k) :
    ∃ m : ℕ,
      polynomialRootPowers (integerMinimalPolynomial x) k =
        integerMinimalPolynomial (x ^ k) ^ m ∧
      algebraicDegree x = m * algebraicDegree (x ^ k) := by
  have hxp := isAlgebraic_pow hx k
  obtain ⟨m, he, hd⟩ := integer_rootPowers_eq_pow_of_irreducible
    (integerMinimalPolynomial_isPrimitive hx)
    (integerMinimalPolynomial_leadingCoeff_pos hx)
    (integerMinimalPolynomial_irreducible hxp)
    (integerMinimalPolynomial_leadingCoeff_pos hxp) hk
    (integerMinimalPolynomial_dvd_power_comp hx k)
  exact ⟨m, he, by simpa only [integerMinimalPolynomial_natDegree] using hd⟩

/-- The exact Mahler and degree relations use the same positive multiplicity. -/
theorem exists_mahlerMeasure_power_multiplicity {x : ℝ}
    (hx : IsAlgebraic ℚ x) {k : ℕ} (hk : 0 < k) :
    ∃ m : ℕ, 0 < m ∧
      algebraicDegree x = m * algebraicDegree (x ^ k) ∧
      mahlerMeasure x ^ k = mahlerMeasure (x ^ k) ^ m := by
  obtain ⟨m, he, hd⟩ := integerMinimalPolynomial_rootPowers_eq_pow hx hk
  have hm : 0 < m := by
    have hp := algebraicDegree_pos hx
    by_contra hn
    have hm0 : m = 0 := by omega
    rw [hm0, zero_mul] at hd
    omega
  refine ⟨m, hm, hd, ?_⟩
  have h := congrArg (fun p : ℤ[X] ↦ (p.map (Int.castRingHom ℂ)).mahlerMeasure) he
  rw [polynomialRootPowers_map (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int,
    polynomialRootPowers_mahlerMeasure, Polynomial.map_pow,
    polynomial_mahlerMeasure_pow] at h
  exact h

/-- The height identity used in the revised paper's power selection, for every
real algebraic number and positive integer power. Both degrees are canonical. -/
theorem log_mahlerMeasure_div_degree_pow {x : ℝ}
    (hx : IsAlgebraic ℚ x) {k : ℕ} (hk : 0 < k) :
    Real.log (mahlerMeasure (x ^ k)) / (algebraicDegree (x ^ k) : ℝ) =
      (k : ℝ) * (Real.log (mahlerMeasure x) / (algebraicDegree x : ℝ)) := by
  obtain ⟨m, hm, hd, hM⟩ := exists_mahlerMeasure_power_multiplicity hx hk
  have hd0 : (algebraicDegree x : ℝ) ≠ 0 := by
    exact_mod_cast (algebraicDegree_pos hx).ne'
  have hdp0 : (algebraicDegree (x ^ k) : ℝ) ≠ 0 := by
    exact_mod_cast (algebraicDegree_pos (isAlgebraic_pow hx k)).ne'
  have hdr : (algebraicDegree x : ℝ) = (m : ℝ) * algebraicDegree (x ^ k) :=
    by exact_mod_cast hd
  have hl := congrArg Real.log hM
  rw [Real.log_pow, Real.log_pow] at hl
  rw [← mul_div_assoc]
  apply (div_eq_div_iff hdp0 hd0).mpr
  calc
    _ = ((m : ℝ) * Real.log (mahlerMeasure (x ^ k))) * algebraicDegree (x ^ k) := by
      rw [hdr]
      ring
    _ = _ := by rw [← hl]

end LpSelfSimilar.Algebraic
