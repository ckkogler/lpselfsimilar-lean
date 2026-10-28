module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Tactic

@[expose] public section

/-!
Canonical primitive integer representatives of rational polynomials.

Denominators are cleared, content is removed, and the leading coefficient is
normalized to be positive. Uniqueness shows independence from the auxiliary
choice made by denominator clearing. Zero is represented by zero. Applying this
construction to the rational minimal polynomial will handle algebraic numbers
which are not algebraic integers, including all relevant rational parameters.
-/

open Polynomial IsLocalization
open scoped nonZeroDivisors

namespace LpSelfSimilar.Algebraic

/-- Positive leading coefficient is the integer-polynomial normalization used
by the canonical representative. -/
lemma normalize_eq_self_of_leadingCoeff_nonneg {p : ℤ[X]}
    (hp : 0 ≤ p.leadingCoeff) : normalize p = p := by
  rw [normalize_apply, Polynomial.coe_normUnit, Int.normUnit_eq, ite_eq_left hp]
  simp

/-- The normalized primitive integer polynomial in a rational association class. -/
noncomputable def primitiveRepresentative (p : ℚ[X]) : ℤ[X] :=
  if p = 0 then 0 else normalize (integerNormalization ℤ⁰ p).primPart

@[simp] lemma primitiveRepresentative_zero : primitiveRepresentative 0 = 0 := by
  simp [primitiveRepresentative]

lemma primitiveRepresentative_isPrimitive {p : ℚ[X]} (hp : p ≠ 0) :
    (primitiveRepresentative p).IsPrimitive := by
  rw [primitiveRepresentative, ite_eq_right hp]
  exact isPrimitive_of_dvd (integerNormalization ℤ⁰ p).isPrimitive_primPart
    (normalize_associated _).dvd

@[simp] lemma normalize_primitiveRepresentative (p : ℚ[X]) :
    normalize (primitiveRepresentative p) = primitiveRepresentative p := by
  classical
  by_cases hp : p = 0 <;> simp [primitiveRepresentative, hp]

/-- Clearing denominators and removing content changes only a rational unit. -/
lemma primitiveRepresentative_map_associated (p : ℚ[X]) :
    Associated ((primitiveRepresentative p).map (algebraMap ℤ ℚ)) p := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  let g := integerNormalization ℤ⁰ p
  have hg : g ≠ 0 := fun h ↦ hp (IsFractionRing.integerNormalization_eq_zero_iff.mp h)
  obtain ⟨a, ha, he⟩ := integerNormalization_spec ℤ⁰ p
  have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero ha
  have hraw : Associated (g.map (algebraMap ℤ ℚ)) p := by
    change Associated ((integerNormalization ℤ⁰ p).map (algebraMap ℤ ℚ)) p
    rw [he, ← IsScalarTower.algebraMap_smul ℚ a p, smul_eq_C_mul]
    exact associated_unit_mul_left p (C (a : ℚ))
      (isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha0))
  have hc : (g.content : ℚ) ≠ 0 := by
    exact_mod_cast (content_eq_zero_iff.not.mpr hg)
  have hprim : Associated (g.primPart.map (algebraMap ℤ ℚ)) (g.map (algebraMap ℤ ℚ)) := by
    conv_rhs => rw [g.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
    exact associated_unit_mul_right _ _ (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))
  rw [primitiveRepresentative, ite_eq_right hp]
  exact (Associated.map (mapRingHom (algebraMap ℤ ℚ)) (normalize_associated g.primPart)).trans
    (hprim.trans hraw)

lemma primitiveRepresentative_natDegree (p : ℚ[X]) :
    (primitiveRepresentative p).natDegree = p.natDegree := by
  have h := natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated (primitiveRepresentative_map_associated p))
  rwa [natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int] at h

lemma primitiveRepresentative_leadingCoeff_pos {p : ℚ[X]} (hp : p ≠ 0) :
    0 < (primitiveRepresentative p).leadingCoeff := by
  rw [primitiveRepresentative, ite_eq_right hp, leadingCoeff_normalize, ← Int.abs_eq_normalize]
  exact abs_pos.mpr (leadingCoeff_ne_zero.mpr (integerNormalization ℤ⁰ p).primPart_ne_zero)

/-- The normalized primitive representative is independent of denominator choices. -/
theorem eq_primitiveRepresentative_of_associated {p : ℚ[X]} (hp : p ≠ 0)
    {q : ℤ[X]} (hq : q.IsPrimitive) (hn : normalize q = q)
    (ha : Associated (q.map (algebraMap ℤ ℚ)) p) : q = primitiveRepresentative p := by
  have hr := primitiveRepresentative_isPrimitive hp
  have hh := ha.trans (primitiveRepresentative_map_associated p).symm
  have hqr : q ∣ primitiveRepresentative p :=
    (hq.dvd_iff_fraction_map_dvd_fraction_map (K := ℚ)).2 hh.dvd
  have hrq : primitiveRepresentative p ∣ q :=
    (hr.dvd_iff_fraction_map_dvd_fraction_map (K := ℚ)).2 hh.dvd'
  have he := normalize_eq_normalize_iff_associated.mpr (associated_of_dvd_dvd hqr hrq)
  simpa only [hn, normalize_primitiveRepresentative] using he

end LpSelfSimilar.Algebraic
