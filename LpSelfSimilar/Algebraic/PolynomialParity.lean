module

public import LpSelfSimilar.Algebraic.PrimitivePolynomial
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Group.Irreducible.Lemmas

@[expose] public section

/-!
# Integer polynomial parity and reflection

Reflection in the indeterminate multiplies the nth coefficient by (-1)^n.
A reflection-invariant integer polynomial therefore expands from its even
coefficients. Reflection preserves irreducibility and primitivity. For a
polynomial with nonzero constant coefficient, association with its reflection
forces actual equality, so a non-even irreducible polynomial and its reflection
have no common irreducible factor.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- Coefficients under reflection of the indeterminate. -/
theorem polynomial_comp_neg_X_coeff (p : ℤ[X]) (n : ℕ) :
    (p.comp (-X)).coeff n = p.coeff n * (-1) ^ n := by
  rw [show (-X : ℤ[X]) = C (-1) * X by simp, comp_C_mul_X_coeff]

/-- A reflection-invariant integer polynomial has no odd-degree coefficients. -/
theorem polynomial_coeff_eq_zero_of_reflection {p : ℤ[X]} (hp : p.comp (-X) = p)
    {n : ℕ} (hn : ¬ 2 ∣ n) : p.coeff n = 0 := by
  have ho : Odd n := Nat.not_even_iff_odd.mp (fun he => hn he.two_dvd)
  have h := congrArg (fun q : ℤ[X] => q.coeff n) hp
  rw [polynomial_comp_neg_X_coeff, ho.neg_one_pow] at h
  linarith

/-- An even integer polynomial is exactly the expansion of its even coefficients. -/
theorem polynomial_expand_contract_two {p : ℤ[X]} (hp : p.comp (-X) = p) :
    expand ℤ 2 (contract 2 p) = p := by
  ext n
  rw [coeff_expand (by norm_num : 0 < (2 : ℕ))]
  by_cases hn : 2 ∣ n
  · rw [ite_eq_left hn, coeff_contract (by decide : (2 : ℕ) ≠ 0), Nat.div_mul_cancel hn]
  · rw [ite_eq_right hn, polynomial_coeff_eq_zero_of_reflection hp hn]

/-- Substitution of X squared always produces an even polynomial. -/
theorem polynomial_expand_two_reflection (p : ℤ[X]) :
    (expand ℤ 2 p).comp (-X) = expand ℤ 2 p := by
  rw [expand_eq_comp_X_pow, comp_assoc]
  simp only [pow_comp, X_comp, neg_sq]

/-- A polynomial times its reflection is even. -/
theorem polynomial_product_reflection (p : ℤ[X]) :
    (p * p.comp (-X)).comp (-X) = p * p.comp (-X) := by
  rw [mul_comp_neg_X, comp_neg_X_comp_neg_X, mul_comm]

/-- A nonzero constant coefficient fixes the unit in an association with reflection. -/
theorem polynomial_reflection_eq_of_associated {p : ℤ[X]} (hp0 : p.coeff 0 ≠ 0)
    (ha : Associated p (p.comp (-X))) : p.comp (-X) = p := by
  obtain ⟨v, hv⟩ := ha
  obtain ⟨c, hc, he⟩ := Polynomial.isUnit_iff.mp v.isUnit
  rw [← he] at hv
  have h := congrArg (fun q : ℤ[X] => q.coeff 0) hv
  rw [coeff_mul_C, polynomial_comp_neg_X_coeff, pow_zero, mul_one] at h
  have hc1 : c = 1 := (mul_left_cancel₀ hp0) (by simpa using h)
  simpa [hc1] using hv.symm

/-- Reflection preserves integer-polynomial irreducibility. -/
theorem irreducible_polynomial_reflection {p : ℤ[X]} (hp : Irreducible p) :
    Irreducible (p.comp (-X)) := by
  change Irreducible ((algEquivAevalNegX (R := ℤ)) p)
  exact hp.map (algEquivAevalNegX (R := ℤ))

/-- A non-even irreducible polynomial with nonzero constant coefficient cannot divide its reflection. -/
theorem polynomial_not_dvd_reflection {p : ℤ[X]} (hp : Irreducible p)
    (hp0 : p.coeff 0 ≠ 0) (hne : p.comp (-X) ≠ p) : ¬ p ∣ p.comp (-X) := by
  intro hd
  exact hne (polynomial_reflection_eq_of_associated hp0
    (hp.associated_of_dvd (irreducible_polynomial_reflection hp) hd))

/-- Reflection preserves primitivity over the integers. -/
theorem isPrimitive_polynomial_reflection {p : ℤ[X]} (hp : p.IsPrimitive) :
    (p.comp (-X)).IsPrimitive := by
  intro c hc
  apply hp c
  have h := (dvd_comp_neg_X_iff (C c) p).mp hc
  simpa only [C_comp] using h

/-- Expanding the indeterminate by a positive integer preserves primitivity. -/
theorem isPrimitive_polynomial_expand {p : ℤ[X]} (hp : p.IsPrimitive)
    {k : ℕ} (hk : 0 < k) : (expand ℤ k p).IsPrimitive := by
  intro c hc
  apply hp c
  apply (C_dvd_iff_dvd_coeff c p).mpr
  intro n
  have h := (C_dvd_iff_dvd_coeff c (expand ℤ k p)).mp hc (n * k)
  simpa only [coeff_expand_mul hk] using h

end LpSelfSimilar.Algebraic
