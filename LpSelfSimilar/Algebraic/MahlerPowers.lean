module

public import LpSelfSimilar.Algebraic.DegreePowers
public import LpSelfSimilar.Algebraic.MahlerMeasure
public import LpSelfSimilar.Analysis.PolynomialMahlerPowers
public import LpSelfSimilar.Analysis.PolynomialRootPowers
public import LpSelfSimilar.Algebraic.PolynomialSeparation

@[expose] public section

/-!
Canonical Mahler measures under powers.

An integer polynomial vanishing at x^k yields one vanishing at x by substituting
X^k. The primitive integer minimal polynomial of x divides it over the integers.
Multiplicativity and the lower bound one for every nonzero integer polynomial
then show M(x) <= M(x^k). No monicity or algebraic-integrality assumption is used.
The complementary upper bound comes from an actual integer resultant polynomial
whose roots are the powers of the original roots and whose Mahler measure is M^k.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- Integer divisibility makes genuine Mahler measure monotone on nonzero
integer polynomials; the integer quotient has Mahler measure at least one. -/
lemma integerPolynomial_mahlerMeasure_le_of_dvd {p q : ℤ[X]}
    (hq : q ≠ 0) (hpq : p ∣ q) :
    (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤
      (q.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨r, rfl⟩ := hpq
  have hr : r ≠ 0 := by
    intro he
    exact hq (by rw [he, mul_zero])
  rw [Polynomial.map_mul, Polynomial.mahlerMeasure_mul]
  exact le_mul_of_one_le_right (Polynomial.mahlerMeasure_nonneg _)
    (Polynomial.one_le_mahlerMeasure_of_ne_zero hr)

/-- Exact integer divisibility for the minimal polynomial of a power. -/
theorem integerMinimalPolynomial_dvd_power_comp {x : ℝ}
    (hx : IsAlgebraic ℚ x) (k : ℕ) :
    integerMinimalPolynomial x ∣ (integerMinimalPolynomial (x ^ k)).comp (X ^ k) := by
  apply (integerMinimalPolynomial_dvd_iff hx).mpr
  rw [aeval_comp, map_pow, aeval_X, integerMinimalPolynomial_aeval]

/-- The Mahler measure cannot decrease on taking a positive integer power. -/
theorem mahlerMeasure_le_pow {x : ℝ} (hx : IsAlgebraic ℚ x)
    {k : ℕ} (hk : 0 < k) : mahlerMeasure x ≤ mahlerMeasure (x ^ k) := by
  have hq : (integerMinimalPolynomial (x ^ k)).comp (X ^ k) ≠ 0 :=
    (Polynomial.expand_eq_zero hk).not.mpr
      (integerMinimalPolynomial_ne_zero (isAlgebraic_pow hx k))
  have h := integerPolynomial_mahlerMeasure_le_of_dvd hq
    (integerMinimalPolynomial_dvd_power_comp hx k)
  rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
    polynomial_mahlerMeasure_comp_X_pow _ hk] at h
  exact h

/-- The canonical integer minimal polynomial of a power divides the actual
root-power resultant of the original canonical polynomial. -/
theorem integerMinimalPolynomial_pow_dvd_rootPowers {x : ℝ}
    (hx : IsAlgebraic ℚ x) (k : ℕ) :
    integerMinimalPolynomial (x ^ k) ∣ polynomialRootPowers (integerMinimalPolynomial x) k := by
  apply (integerMinimalPolynomial_dvd_iff (isAlgebraic_pow hx k)).mpr
  have hn : (integerMinimalPolynomial x).map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_eq_zero_iff (Int.castRingHom ℂ).injective_int).not.mpr
      (integerMinimalPolynomial_ne_zero hx)
  have hr : ((integerMinimalPolynomial x).map (Int.castRingHom ℂ)).IsRoot (x : ℂ) := by
    rw [IsRoot, integerPolynomial_complex_eval, integerMinimalPolynomial_aeval,
      Complex.ofReal_zero]
  have h := polynomialRootPowers_isRoot hn hr k
  rw [← polynomialRootPowers_map (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int,
    IsRoot, ← Complex.ofReal_pow, integerPolynomial_complex_eval] at h
  exact_mod_cast h

/-- The Mahler measure of a power is at most the original measure to that power. -/
theorem mahlerMeasure_pow_le {x : ℝ} (hx : IsAlgebraic ℚ x)
    (k : ℕ) : mahlerMeasure (x ^ k) ≤ mahlerMeasure x ^ k := by
  have he : ((polynomialRootPowers (integerMinimalPolynomial x) k).map
      (Int.castRingHom ℂ)).mahlerMeasure = mahlerMeasure x ^ k := by
    rw [polynomialRootPowers_map (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int,
      polynomialRootPowers_mahlerMeasure]
    rfl
  have hq : polynomialRootPowers (integerMinimalPolynomial x) k ≠ 0 := by
    intro hz
    have hp : 0 < mahlerMeasure x ^ k := pow_pos (lt_of_lt_of_le zero_lt_one
      (one_le_mahlerMeasure hx)) k
    rw [hz, Polynomial.map_zero, Polynomial.mahlerMeasure_zero] at he
    linarith
  exact (integerPolynomial_mahlerMeasure_le_of_dvd hq
    (integerMinimalPolynomial_pow_dvd_rootPowers hx k)).trans_eq he

end LpSelfSimilar.Algebraic
