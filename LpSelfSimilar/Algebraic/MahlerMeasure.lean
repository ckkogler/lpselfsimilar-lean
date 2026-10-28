module

public import LpSelfSimilar.Algebraic.MinimalPolynomial
public import Mathlib.NumberTheory.MahlerMeasure

@[expose] public section

/-!
The genuine Mahler measure of a real algebraic number.

This is Mathlib's exponential circle-average Mahler measure applied to the
canonical primitive integer minimal polynomial. The product over complex roots
is proved equal to this definition. Nonzero integer polynomials have measure at
least one; for an algebraic real number strictly between zero and one, equality
is excluded by Mathlib's proved Kronecker theorem.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- The Mahler measure of the canonical primitive integer minimal polynomial. -/
noncomputable def mahlerMeasure (x : ℝ) : ℝ :=
  ((integerMinimalPolynomial x).map (Int.castRingHom ℂ)).mahlerMeasure

/-- The paper's product formula, with roots counted with multiplicity and the
positive integer leading coefficient kept explicitly. -/
theorem mahlerMeasure_eq_leadingCoeff_mul_prod_aroots {x : ℝ}
    (hx : IsAlgebraic ℚ x) :
    mahlerMeasure x = ((integerMinimalPolynomial x).leadingCoeff : ℝ) *
      (((integerMinimalPolynomial x).aroots ℂ).map (fun z ↦ max 1 ‖z‖)).prod := by
  rw [mahlerMeasure, Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int]
  have hpos : (0 : ℝ) < (integerMinimalPolynomial x).leadingCoeff :=
    by exact_mod_cast integerMinimalPolynomial_leadingCoeff_pos hx
  simp only [Int.coe_castRingHom, Complex.norm_intCast, abs_of_pos hpos]
  rfl

lemma one_le_mahlerMeasure {x : ℝ} (hx : IsAlgebraic ℚ x) :
    1 ≤ mahlerMeasure x :=
  Polynomial.one_le_mahlerMeasure_of_ne_zero (integerMinimalPolynomial_ne_zero hx)

/-- A contracting positive algebraic number is not a root of unity, so its
canonical Mahler measure is strictly greater than one. -/
lemma one_lt_mahlerMeasure {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : 1 < mahlerMeasure x := by
  have hle := one_le_mahlerMeasure hx
  apply lt_of_le_of_ne hle
  intro he
  have hroot : (x : ℂ) ∈ (integerMinimalPolynomial x).aroots ℂ :=
    mem_aroots.mpr ⟨integerMinimalPolynomial_ne_zero hx,
      integerMinimalPolynomial_complex_aeval x⟩
  obtain ⟨n, hn, heq⟩ := Polynomial.pow_eq_one_of_mahlerMeasure_eq_one
    (show ((integerMinimalPolynomial x).map (Int.castRingHom ℂ)).mahlerMeasure = 1
      from he.symm) (by exact_mod_cast hx0.ne') hroot
  have hxpow : x ^ n = 1 := by exact_mod_cast heq
  have hlt : x ^ n < 1 := pow_lt_one₀ hx0.le hx1 hn.ne'
  linarith

lemma log_mahlerMeasure_pos {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : 0 < Real.log (mahlerMeasure x) :=
  Real.log_pos (one_lt_mahlerMeasure hx hx0 hx1)

end LpSelfSimilar.Algebraic
