module

public import LpSelfSimilar.Algebraic.RootPowerPrimitivity
public import LpSelfSimilar.Algebraic.PrimitivePolynomial

@[expose] public section

/-!
Exact integer factorization of root-power resultants.

An integer root-power resultant has its original degree and leading coefficient
raised to the power. If the input is primitive and divides q(X^k), the resultant
divides q^degree over the integers: the complex root-factor divisibility descends
through the rationals by Gauss's lemma. For irreducible q, unique factorization
therefore identifies the resultant, up to a unit, with a power of q. Positive
leading coefficients remove that last unit. These are the normalization and
multiplicity facts required by the height identity.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

lemma integer_rootPowers_leadingCoeff (p : ℤ[X]) (k : ℕ) :
    (polynomialRootPowers p k).leadingCoeff = p.leadingCoeff ^ k := by
  apply (Int.castRingHom ℂ).injective_int
  rw [← leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int,
    polynomialRootPowers_map (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int,
    polynomialRootPowers_leadingCoeff_of_splits _ (IsAlgClosed.splits _) k,
    leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int, map_pow]

lemma integer_rootPowers_natDegree {p : ℤ[X]} (hp : p ≠ 0) (k : ℕ) :
    (polynomialRootPowers p k).natDegree = p.natDegree := by
  have hm : p.map (Int.castRingHom ℂ) ≠ 0 :=
    (Polynomial.map_eq_zero_iff (Int.castRingHom ℂ).injective_int).not.mpr hp
  have h := polynomialRootPowers_natDegree_of_splits hm (IsAlgClosed.splits _) k
  rw [← polynomialRootPowers_map (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int,
    natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int,
    natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int] at h
  exact h

/-- Gauss descent keeps the divisibility over the integers, so a rational
leading scalar cannot silently change the Mahler measure. -/
theorem integer_rootPowers_dvd_pow_of_dvd_comp {p q : ℤ[X]} (hp : p.IsPrimitive)
    {k : ℕ} (hk : 0 < k) (hd : p ∣ q.comp (X ^ k)) :
    polynomialRootPowers p k ∣ q ^ p.natDegree := by
  apply ((polynomialRootPowers_isPrimitive hp hk).dvd_iff_fraction_map_dvd_fraction_map
    (K := ℚ)).mpr
  apply (Polynomial.map_dvd_map' (algebraMap ℚ ℂ)).mp
  have hmap : (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ) = Int.castRingHom ℂ := by
    ext z
    simp
  rw [Polynomial.map_map, Polynomial.map_map, hmap,
    polynomialRootPowers_map (Int.castRingHom ℂ) (Int.castRingHom ℂ).injective_int,
    Polynomial.map_pow]
  have hd' := Polynomial.map_dvd (Int.castRingHom ℂ) hd
  rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X] at hd'
  have h := polynomialRootPowers_dvd_pow_of_dvd_comp
    ((Polynomial.map_eq_zero_iff (Int.castRingHom ℂ).injective_int).not.mpr hp.ne_zero) k hd'
  rwa [natDegree_map_eq_of_injective (Int.castRingHom ℂ).injective_int] at h

/-- Primitivity and irreducibility force one repeated integer factor. The
degree equation records its multiplicity without assuming equal conjugate fibers. -/
theorem integer_rootPowers_eq_pow_of_irreducible {p q : ℤ[X]}
    (hp : p.IsPrimitive) (hp0 : 0 < p.leadingCoeff) (hq : Irreducible q)
    (hq0 : 0 < q.leadingCoeff) {k : ℕ} (hk : 0 < k)
    (hd : p ∣ q.comp (X ^ k)) :
    ∃ m : ℕ, polynomialRootPowers p k = q ^ m ∧ p.natDegree = m * q.natDegree := by
  obtain ⟨m, hm, ha⟩ := (dvd_prime_pow hq.prime p.natDegree).mp
    (integer_rootPowers_dvd_pow_of_dvd_comp hp hk hd)
  have he : polynomialRootPowers p k = q ^ m := ha.eq_of_normalized
    (normalize_eq_self_of_leadingCoeff_nonneg (by
      rw [integer_rootPowers_leadingCoeff]
      exact (pow_pos hp0 k).le))
    (normalize_eq_self_of_leadingCoeff_nonneg (by
      rw [leadingCoeff_pow]
      exact (pow_pos hq0 m).le))
  refine ⟨m, he, ?_⟩
  have hn := congrArg Polynomial.natDegree he
  rwa [integer_rootPowers_natDegree hp.ne_zero, natDegree_pow] at hn

end LpSelfSimilar.Algebraic
