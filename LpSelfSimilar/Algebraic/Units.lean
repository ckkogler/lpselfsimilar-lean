module

public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
Algebraic units and roots of height-one integer polynomials.

A real algebraic unit is a nonzero algebraic integer with integral reciprocal.
The equivalence with units of the integral closure makes this meaning explicit.
A height-one polynomial and its reversal prove both integrality conditions for
any nonzero root; these reusable facts do not depend on Bernoulli measures.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- A nonzero real algebraic integer whose inverse is also an algebraic integer.
The explicit nonzero condition excludes the totalized inverse of zero. -/
def IsAlgebraicUnit (x : ℝ) : Prop := x ≠ 0 ∧ IsIntegral ℤ x ∧ IsIntegral ℤ x⁻¹

/-- A height-one integer polynomial is monic up to sign. -/
lemma isIntegral_of_height_one_polynomial {x : ℝ} {p : ℤ[X]} (hp : p ≠ 0)
    (hcoeff : ∀ j, |p.coeff j| ≤ 1) (hx : aeval x p = 0) : IsIntegral ℤ x := by
  have hb : |p.leadingCoeff| ≤ 1 := hcoeff p.natDegree
  have hn : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have he : p.leadingCoeff = 1 ∨ p.leadingCoeff = -1 := by
    have h := abs_le.mp hb
    omega
  rcases he with he | he
  · exact ⟨p, he, hx⟩
  · refine ⟨-p, ?_, ?_⟩
    · change (-p).leadingCoeff = 1
      rw [leadingCoeff_neg, he]
      norm_num
    · change aeval x (-p) = 0
      rw [map_neg, hx, neg_zero]

/-- Reversal retains the height-one coefficient bound and exchanges a nonzero
root with its reciprocal. -/
lemma isAlgebraicUnit_of_height_one_polynomial {x : ℝ} (hx0 : x ≠ 0)
    {p : ℤ[X]} (hp : p ≠ 0) (hcoeff : ∀ j, |p.coeff j| ≤ 1)
    (hx : aeval x p = 0) : IsAlgebraicUnit x := by
  let : Invertible x := invertibleOfNonzero hx0
  refine ⟨hx0, isIntegral_of_height_one_polynomial hp hcoeff hx, ?_⟩
  apply isIntegral_of_height_one_polynomial (show p.reverse ≠ 0 by simpa using hp)
    (fun j ↦ by rw [coeff_reverse]; exact hcoeff _)
  have h := (eval₂_reverse_eq_zero_iff (algebraMap ℤ ℝ) x p).mpr hx
  simpa only [invOf_eq_inv, ← aeval_def] using h

/-- Equivalence with genuine units in the ring of real algebraic integers. -/
theorem isAlgebraicUnit_iff_exists_integralClosure_unit (x : ℝ) :
    IsAlgebraicUnit x ↔ ∃ u : (integralClosure ℤ ℝ)ˣ,
      ((u : integralClosure ℤ ℝ) : ℝ) = x := by
  constructor
  · rintro ⟨hx0, hx, hxi⟩
    refine ⟨⟨⟨x, hx⟩, ⟨x⁻¹, hxi⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      exact mul_inv_cancel₀ hx0
    · apply Subtype.ext
      exact inv_mul_cancel₀ hx0
  · rintro ⟨u, rfl⟩
    have hu : IsUnit ((u : integralClosure ℤ ℝ) : ℝ) :=
      u.isUnit.map (algebraMap (integralClosure ℤ ℝ) ℝ)
    refine ⟨hu.ne_zero, (u : integralClosure ℤ ℝ).property, ?_⟩
    have hi : (((u⁻¹ : (integralClosure ℤ ℝ)ˣ) : integralClosure ℤ ℝ) : ℝ) =
        (((u : integralClosure ℤ ℝ) : ℝ))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      exact congrArg (fun y : integralClosure ℤ ℝ ↦ (y : ℝ)) u.inv_val
    rw [← hi]
    exact ((u⁻¹ : (integralClosure ℤ ℝ)ˣ) : integralClosure ℤ ℝ).property

end LpSelfSimilar.Algebraic
