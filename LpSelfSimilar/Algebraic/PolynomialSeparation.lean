module

public import LpSelfSimilar.Algebraic.ResultantBound
public import LpSelfSimilar.Algebraic.Complexity

@[expose] public section

/-!
The algebraic separation inequality for integer polynomials of height at most one.

Irreducibility over the rationals makes the resultant with the canonical minimal
polynomial nonzero whenever the given evaluation is nonzero. The resultant is an
actual integer, so its absolute value is at least one. The analytic resultant
bound then gives the precise degree and Mahler factors used in Lemma 3.6.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- Nonvanishing is proved over the rational field, then transferred to the
integer determinant; coprimality over the integer polynomial ring is not assumed. -/
lemma integerMinimalPolynomial_resultant_ne_zero {x : ℝ} (hx : IsAlgebraic ℚ x)
    {p : ℤ[X]} (hp : aeval x p ≠ 0) :
    (integerMinimalPolynomial x).resultant p ≠ 0 := by
  let f := (integerMinimalPolynomial x).map (algebraMap ℤ ℚ)
  let g := p.map (algebraMap ℤ ℚ)
  have hirr : Irreducible f :=
    (integerMinimalPolynomial_map_associated x).irreducible_iff.mpr
      (minpoly.irreducible hx.isIntegral)
  have hcop : IsCoprime f g := hirr.coprime_iff_not_dvd.mpr (by
    intro hdiv
    have hzero : aeval x f = 0 := by
      change aeval x ((integerMinimalPolynomial x).map (algebraMap ℤ ℚ)) = 0
      rw [aeval_map_algebraMap, integerMinimalPolynomial_aeval]
    have h := aeval_eq_zero_of_dvd_aeval_eq_zero hdiv hzero
    exact hp (by simpa only [g, aeval_map_algebraMap] using h))
  have hne := resultant_ne_zero f g hcop
  intro he
  apply hne
  change ((integerMinimalPolynomial x).map (algebraMap ℤ ℚ)).resultant
    (p.map (algebraMap ℤ ℚ)) = 0
  rw [natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int,
    natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int,
    resultant_map_map, he, map_zero]

/-- Evaluating after complexification agrees with the real evaluation embedded
in C; this keeps every later norm estimate tied to the original real parameter. -/
lemma integerPolynomial_complex_eval (p : ℤ[X]) (x : ℝ) :
    (p.map (Int.castRingHom ℂ)).eval (x : ℂ) = (aeval x p : ℝ) := by
  change (p.map (algebraMap ℤ ℂ)).eval (algebraMap ℝ ℂ x) = _
  rw [eval_map_algebraMap, aeval_algebraMap_apply]
  rfl

/-- The exact multiplicative separation inequality before division. -/
theorem one_le_abs_eval_mul_degree_mahler {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) {p : ℤ[X]} (hp : aeval x p ≠ 0)
    (hcoeff : ∀ j, |p.coeff j| ≤ 1) :
    1 ≤ |aeval x p| * ((p.natDegree : ℝ) + 1) ^ (algebraicDegree x - 1) *
      mahlerMeasure x ^ p.natDegree := by
  let f := (integerMinimalPolynomial x).map (Int.castRingHom ℂ)
  let g := p.map (Int.castRingHom ℂ)
  have hf : f ≠ 0 := (Polynomial.map_ne_zero_iff (Int.castRingHom ℂ).injective_int).mpr
    (integerMinimalPolynomial_ne_zero hx)
  have hz : f.IsRoot (x : ℂ) := by
    change f.eval (x : ℂ) = 0
    rw [integerPolynomial_complex_eval, integerMinimalPolynomial_aeval, Complex.ofReal_zero]
  have hg : ∀ j, ‖g.coeff j‖ ≤ (1 : ℝ) := by
    intro j
    dsimp [g]
    rw [coeff_map, Int.coe_castRingHom, Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast hcoeff j
  have hbound := norm_resultant_le_of_root g f hf (by norm_num : (0 : ℝ) ≤ 1) hg hz
    (by simpa [abs_of_pos hx0] using hx1.le)
  have hdegf : f.natDegree = algebraicDegree x := by
    rw [natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int,
      integerMinimalPolynomial_natDegree]
  have hdegg : g.natDegree = p.natDegree :=
    natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int p
  have hres : f.resultant g =
      (((integerMinimalPolynomial x).resultant p : ℤ) : ℂ) := by
    dsimp [f, g]
    rw [natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int,
      natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int, resultant_map_map]
    rfl
  have hlow : (1 : ℝ) ≤ ‖f.resultant g‖ := by
    rw [hres, Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs (integerMinimalPolynomial_resultant_ne_zero hx hp)
  rw [hres] at hlow hbound
  rw [hdegf, hdegg, mul_one, integerPolynomial_complex_eval,
    Complex.norm_real, Real.norm_eq_abs] at hbound
  exact hlow.trans hbound

/-- The paper's (n+1)^(1-d) M^(-n), expressed with ordinary real division
and nonnegative integer exponents. The algebraic degree is proved positive. -/
theorem abs_eval_ge_inverse_degree_mahler {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) {p : ℤ[X]} (hp : aeval x p ≠ 0)
    (hcoeff : ∀ j, |p.coeff j| ≤ 1) :
    1 / (((p.natDegree : ℝ) + 1) ^ (algebraicDegree x - 1) *
      mahlerMeasure x ^ p.natDegree) ≤ |aeval x p| := by
  have hM : 0 < mahlerMeasure x := zero_lt_one.trans_le (one_le_mahlerMeasure hx)
  apply (div_le_iff₀ (by positivity)).mpr
  simpa only [mul_assoc] using one_le_abs_eval_mul_degree_mahler hx hx0 hx1 hp hcoeff

end LpSelfSimilar.Algebraic
