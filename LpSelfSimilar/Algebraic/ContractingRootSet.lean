module

public import LpSelfSimilar.Algebraic.ContractingConjugates
public import Mathlib.FieldTheory.Separable

@[expose] public section

/-!
# The finite set of distinct contracting conjugates

Characteristic-zero separability removes multiplicities from the canonical
minimal polynomial. Integer coefficients make conjugation preserve its roots
and the unit-disk filter. The finite root set therefore retains the exact
Mahler product already proved for the multiset. These facts are the arithmetic
inputs to the real block representation; no choice of roots is assumed.
-/

open Polynomial Complex
open scoped ComplexConjugate

namespace LpSelfSimilar.Algebraic

/-- The canonical integer polynomial, viewed over the complex numbers, is separable. -/
theorem integerMinimalPolynomial_complex_separable {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ((integerMinimalPolynomial x).map (algebraMap ℤ ℂ)).Separable := by
  have hq : ((integerMinimalPolynomial x).map (algebraMap ℤ ℚ)).Separable :=
    (integerMinimalPolynomial_map_associated x).separable_iff.mpr
      (minpoly.irreducible hx.isIntegral).separable
  have hc := hq.map (f := algebraMap ℚ ℂ)
  simpa only [map_map, ← IsScalarTower.algebraMap_eq ℤ ℚ ℂ] using hc

theorem integerMinimalPolynomial_aroots_nodup {x : ℝ} (hx : IsAlgebraic ℚ x) :
    ((integerMinimalPolynomial x).aroots ℂ).Nodup :=
  Polynomial.nodup_roots (integerMinimalPolynomial_complex_separable hx)

theorem contractingConjugates_nodup {x : ℝ} (hx : IsAlgebraic ℚ x) :
    (contractingConjugates x).Nodup := by
  classical
  exact (integerMinimalPolynomial_aroots_nodup hx).filter _

/-- Conjugation commutes with evaluation of every integer polynomial. -/
theorem integerPolynomial_aeval_conj (P : ℤ[X]) (z : ℂ) :
    aeval (conj z) P = conj (aeval z P) := by
  exact aeval_algHom_apply (Complex.conjAe.restrictScalars ℤ) z P

theorem conj_mem_contractingConjugates_iff {x : ℝ} {z : ℂ} :
    conj z ∈ contractingConjugates x ↔ z ∈ contractingConjugates x := by
  rw [mem_contractingConjugates, mem_contractingConjugates, mem_aroots, mem_aroots,
    integerPolynomial_aeval_conj, map_eq_zero, Complex.norm_conj]

/-- The canonical finite set, with no repeated roots. -/
noncomputable def contractingRootSet (x : ℝ) : Finset ℂ :=
  (contractingConjugates x).toFinset

@[simp] theorem mem_contractingRootSet {x : ℝ} {z : ℂ} :
    z ∈ contractingRootSet x ↔ z ∈ contractingConjugates x := by
  classical
  exact Multiset.mem_toFinset

@[simp] theorem conj_mem_contractingRootSet_iff {x : ℝ} {z : ℂ} :
    conj z ∈ contractingRootSet x ↔ z ∈ contractingRootSet x := by
  simp only [mem_contractingRootSet, conj_mem_contractingConjugates_iff]

theorem contractingRootSet_nonempty {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : (contractingRootSet x).Nonempty :=
  ⟨(x : ℂ), mem_contractingRootSet.mpr (self_mem_contractingConjugates hx hx0 hx1)⟩

/-- Deduplicating the roots does not alter the canonical determinant modulus. -/
theorem prod_contractingRootSet_norms {x : ℝ} (hx : IsAlgebraicUnit x) :
    ∏ z ∈ contractingRootSet x, ‖z‖ = (mahlerMeasure x)⁻¹ := by
  classical
  have ha : IsAlgebraic ℚ x := (hx.2.1.tower_top (A := ℚ)).isAlgebraic
  have hval : (contractingRootSet x).val = contractingConjugates x := by
    exact (contractingConjugates_nodup ha).dedup
  change ((contractingRootSet x).val.map (fun z => ‖z‖)).prod = _
  rw [hval]
  exact prod_contractingConjugate_norms_eq_inv_mahlerMeasure hx

end LpSelfSimilar.Algebraic
