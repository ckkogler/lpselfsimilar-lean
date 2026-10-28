module

public import LpSelfSimilar.Algebraic.PrimitivePolynomial
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section

/-!
The canonical integer minimal polynomial and degree of a real algebraic number.

The paper uses the primitive integer polynomial with positive leading coefficient,
including for numbers which are not integral over the integers. We therefore
start from Mathlib's minimal polynomial over the rationals and use its unique
primitive integer representative. The resulting polynomial vanishes at the number,
is irreducible, and divides every integer polynomial vanishing there. All these
properties are proved rather than supplied as data to the arithmetic arguments.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- Primitive, positive-leading integer minimal polynomial; zero for transcendental
real numbers, following the convention for Mathlib's rational minimal polynomial. -/
noncomputable def integerMinimalPolynomial (x : ℝ) : ℤ[X] :=
  primitiveRepresentative (minpoly ℚ x)

/-- Algebraic degree over the rationals, with the usual zero convention outside
the algebraic numbers. -/
noncomputable def algebraicDegree (x : ℝ) : ℕ := (minpoly ℚ x).natDegree

lemma integerMinimalPolynomial_map_associated (x : ℝ) :
    Associated ((integerMinimalPolynomial x).map (algebraMap ℤ ℚ)) (minpoly ℚ x) :=
  primitiveRepresentative_map_associated _

@[simp] lemma integerMinimalPolynomial_natDegree (x : ℝ) :
    (integerMinimalPolynomial x).natDegree = algebraicDegree x :=
  primitiveRepresentative_natDegree _

lemma algebraicDegree_pos {x : ℝ} (hx : IsAlgebraic ℚ x) :
    0 < algebraicDegree x := minpoly.natDegree_pos hx.isIntegral

lemma integerMinimalPolynomial_isPrimitive {x : ℝ} (hx : IsAlgebraic ℚ x) :
    (integerMinimalPolynomial x).IsPrimitive :=
  primitiveRepresentative_isPrimitive (minpoly.ne_zero hx.isIntegral)

lemma integerMinimalPolynomial_leadingCoeff_pos {x : ℝ} (hx : IsAlgebraic ℚ x) :
    0 < (integerMinimalPolynomial x).leadingCoeff :=
  primitiveRepresentative_leadingCoeff_pos (minpoly.ne_zero hx.isIntegral)

lemma integerMinimalPolynomial_ne_zero {x : ℝ} (hx : IsAlgebraic ℚ x) :
    integerMinimalPolynomial x ≠ 0 :=
  leadingCoeff_ne_zero.mp (integerMinimalPolynomial_leadingCoeff_pos hx).ne'

@[simp] lemma normalize_integerMinimalPolynomial (x : ℝ) :
    normalize (integerMinimalPolynomial x) = integerMinimalPolynomial x :=
  normalize_primitiveRepresentative _

lemma integerMinimalPolynomial_irreducible {x : ℝ} (hx : IsAlgebraic ℚ x) :
    Irreducible (integerMinimalPolynomial x) :=
  (integerMinimalPolynomial_isPrimitive hx).irreducible_of_irreducible_map_of_injective
    (algebraMap ℤ ℚ).injective_int
    ((integerMinimalPolynomial_map_associated x).irreducible_iff.mpr
      (minpoly.irreducible hx.isIntegral))

@[simp] lemma integerMinimalPolynomial_aeval (x : ℝ) :
    aeval x (integerMinimalPolynomial x) = 0 := by
  have h := (minpoly.dvd_iff (A := ℚ) (x := x)).mp
    (integerMinimalPolynomial_map_associated x).dvd'
  simpa only [aeval_map_algebraMap] using h

lemma integerMinimalPolynomial_complex_aeval (x : ℝ) :
    aeval (x : ℂ) (integerMinimalPolynomial x) = 0 := by
  change aeval (algebraMap ℝ ℂ x) (integerMinimalPolynomial x) = 0
  rw [aeval_algebraMap_apply, integerMinimalPolynomial_aeval, map_zero]

/-- The rational roots of the canonical integer polynomial are exactly the
parameter itself. This also excludes spurious roots introduced by normalization. -/
lemma integerMinimalPolynomial_rat_root {x : ℝ} (hx : IsAlgebraic ℚ x)
    {r : ℚ} (hr : aeval r (integerMinimalPolynomial x) = 0) : (r : ℝ) = x := by
  apply minpoly.root hx.isIntegral
  have h := aeval_eq_zero_of_dvd_aeval_eq_zero (x := r)
    (integerMinimalPolynomial_map_associated x).dvd
    (by simpa only [aeval_map_algebraMap] using hr)
  simpa [aeval_def, IsRoot] using h

lemma integerMinimalPolynomial_coeff_zero_ne_zero {x : ℝ}
    (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0) :
    (integerMinimalPolynomial x).coeff 0 ≠ 0 := by
  intro hc
  have hr : aeval (0 : ℚ) (integerMinimalPolynomial x) = 0 := by
    rw [aeval_def, eval₂_at_zero, hc, map_zero]
  have he := integerMinimalPolynomial_rat_root hx hr
  exact hx0 (by simpa using he.symm)

lemma integerMinimalPolynomial_eval_one_ne_zero {x : ℝ}
    (hx : IsAlgebraic ℚ x) (hx1 : x ≠ 1) :
    (integerMinimalPolynomial x).eval 1 ≠ 0 := by
  intro he
  have hr : aeval (1 : ℚ) (integerMinimalPolynomial x) = 0 := by
    have h := congrArg (algebraMap ℤ ℚ) he
    simpa only [← aeval_algebraMap_apply_eq_algebraMap_eval, map_one, map_zero] using h
  have h := integerMinimalPolynomial_rat_root hx hr
  exact hx1 (by simpa using h.symm)

/-- Gauss's lemma transfers the rational minimal-polynomial divisibility back
to the canonical primitive integer polynomial. -/
theorem integerMinimalPolynomial_dvd_iff {x : ℝ} (hx : IsAlgebraic ℚ x)
    {p : ℤ[X]} : integerMinimalPolynomial x ∣ p ↔ aeval x p = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [map_mul, integerMinimalPolynomial_aeval, zero_mul]
  · intro hp
    apply ((integerMinimalPolynomial_isPrimitive hx).dvd_iff_fraction_map_dvd_fraction_map
      (K := ℚ)).2
    apply (integerMinimalPolynomial_map_associated x).dvd.trans
    apply minpoly.dvd ℚ x
    simpa only [aeval_map_algebraMap] using hp

end LpSelfSimilar.Algebraic
