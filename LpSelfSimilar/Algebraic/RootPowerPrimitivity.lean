module

public import LpSelfSimilar.Analysis.PolynomialRootPowers
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Int

@[expose] public section

/-!
Primitivity of the integer polynomial that powers all roots.

Reduction modulo a prime can lower the degree of the input polynomial. We retain
the original Sylvester matrix size and account for this drop explicitly. The
additional resultant factor is a sign, because Y-X^k has top coefficient -1.
Thus a nonzero reduction stays nonzero after powering roots. This gives the
primitive integer normalization needed for the exact height identity.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

lemma polynomialRootPowers_ne_zero_of_splits {R : Type*} [CommRing R] [IsDomain R]
    {p : R[X]} (hp : p ≠ 0) (hs : p.Splits) (k : ℕ) :
    polynomialRootPowers p k ≠ 0 := by
  rw [polynomialRootPowers_eq_prod_of_splits p hs k]
  apply mul_ne_zero
  · exact C_ne_zero.mpr (pow_ne_zero k (leadingCoeff_ne_zero.mpr hp))
  · intro he
    obtain ⟨z, hz, hez⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp he)
    exact X_sub_C_ne_zero (z ^ k) hez

lemma polynomialRootPowers_ne_zero {K : Type*} [Field K]
    {p : K[X]} (hp : p ≠ 0) (k : ℕ) : polynomialRootPowers p k ≠ 0 := by
  let φ := algebraMap K p.SplittingField
  have hm : p.map φ ≠ 0 := (Polynomial.map_eq_zero_iff φ.injective).not.mpr hp
  have hn := polynomialRootPowers_ne_zero_of_splits hm (SplittingField.splits p) k
  intro he
  apply hn
  rw [← polynomialRootPowers_map φ φ.injective, he, Polynomial.map_zero]

/-- Coefficient mapping without an injectivity assumption retains the original
degree as the size of the resultant, even if the mapped polynomial loses degree. -/
lemma polynomialRootPowers_map_fixed_degree {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : R[X]) (k : ℕ) :
    (polynomialRootPowers p k).map φ =
      ((p.map φ).map C).resultant (C (X : S[X]) - X ^ k) p.natDegree k := by
  unfold polynomialRootPowers
  change (Polynomial.mapRingHom φ)
    ((p.map C).resultant (C (X : R[X]) - X ^ k) p.natDegree k) = _
  rw [← resultant_map_map _ _ _ _ (Polynomial.mapRingHom φ)]
  have hc : (Polynomial.mapRingHom φ).comp (Polynomial.C : R →+* R[X]) =
      (Polynomial.C : S →+* S[X]).comp φ := by
    ext a
    simp
  congr 1
  · rw [Polynomial.map_map, Polynomial.map_map, hc]
  · simp only [Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, Polynomial.coe_mapRingHom]

/-- Degree loss under a coefficient map only introduces a unit sign. In
particular every nonzero reduction to a field remains nonzero. -/
theorem polynomialRootPowers_map_ne_zero {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) {p : R[X]} (hp : p.map φ ≠ 0) {k : ℕ} (hk : 0 < k) :
    (polynomialRootPowers p k).map φ ≠ 0 := by
  rw [polynomialRootPowers_map_fixed_degree]
  have hd : (p.map φ).natDegree ≤ p.natDegree := natDegree_map_le
  have hc : (C (X : K[X]) - X ^ k).coeff k = -1 := by
    rw [coeff_sub, coeff_C_of_ne_zero hk.ne', coeff_X_pow_self, zero_sub]
  have he := resultant_add_left_deg ((p.map φ).map C)
    (C (X : K[X]) - X ^ k) (p.map φ).natDegree k
    (p.natDegree - (p.map φ).natDegree)
    (by rw [natDegree_map_eq_of_injective C_injective])
  rw [Nat.add_sub_of_le hd, hc] at he
  rw [he]
  apply mul_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  · exact polynomialRootPowers_ne_zero hp k

/-- A primitive integer polynomial remains nonzero modulo every prime. -/
lemma primitive_polynomial_map_zmod_ne_zero {p : ℤ[X]} (hp : p.IsPrimitive)
    {q : ℕ} (hq : q.Prime) : p.map (Int.castRingHom (ZMod q)) ≠ 0 := by
  intro he
  have hd : C (q : ℤ) ∣ p := by
    apply (C_dvd_iff_dvd_coeff _ _).mpr
    intro j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have h := congrArg (fun r : (ZMod q)[X] ↦ r.coeff j) he
    simpa using h
  have hu := hp (q : ℤ) hd
  exact hq.ne_one (by simpa using Int.isUnit_iff_natAbs_eq.mp hu)

/-- Powering the roots preserves primitive integer normalization. The proof
checks every prime reduction, including primes dividing the leading coefficient. -/
theorem polynomialRootPowers_isPrimitive {p : ℤ[X]} (hp : p.IsPrimitive)
    {k : ℕ} (hk : 0 < k) : (polynomialRootPowers p k).IsPrimitive := by
  intro r hr
  by_contra hunit
  obtain ⟨q, hq, hqr⟩ := Nat.exists_prime_and_dvd
    (show r.natAbs ≠ 1 from fun h ↦ hunit (Int.isUnit_iff_natAbs_eq.mpr h))
  let : Fact q.Prime := ⟨hq⟩
  let φ := Int.castRingHom (ZMod q)
  have hφr : φ r = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd r q).mpr
    (Int.natCast_dvd.mpr hqr)
  have hn := polynomialRootPowers_map_ne_zero φ
    (primitive_polynomial_map_zmod_ne_zero hp hq) hk
  apply hn
  obtain ⟨s, hs⟩ := hr
  rw [hs, Polynomial.map_mul, Polynomial.map_C, hφr, C_0, zero_mul]

end LpSelfSimilar.Algebraic
