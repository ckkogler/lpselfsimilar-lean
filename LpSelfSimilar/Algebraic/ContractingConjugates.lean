module

public import LpSelfSimilar.Algebraic.UnitPolynomial
public import LpSelfSimilar.Algebraic.MahlerMeasure

@[expose] public section

/-!
Contracting complex conjugates, counted with their actual polynomial multiplicity.

For an algebraic unit, the product of all conjugate moduli is one. Splitting that
product at modulus one identifies the product of contracting moduli with the
inverse of the canonical Mahler measure. This is the determinant normalization
needed by the Gaussian matrix construction; no root-product formula is assumed.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

/-- Complex conjugates inside the open unit disk, retaining multiplicities. -/
noncomputable def contractingConjugates (x : ℝ) : Multiset ℂ := by
  classical
  exact ((integerMinimalPolynomial x).aroots ℂ).filter (fun z ↦ ‖z‖ < 1)

lemma mem_contractingConjugates {x : ℝ} {z : ℂ} :
    z ∈ contractingConjugates x ↔ z ∈ (integerMinimalPolynomial x).aroots ℂ ∧ ‖z‖ < 1 := by
  classical
  simp [contractingConjugates]

lemma self_mem_contractingConjugates {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) : (x : ℂ) ∈ contractingConjugates x := by
  rw [mem_contractingConjugates]
  refine ⟨mem_aroots.mpr ⟨integerMinimalPolynomial_ne_zero hx,
    integerMinimalPolynomial_complex_aeval x⟩, ?_⟩
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0] using hx1

lemma contractingConjugate_ne_zero {x : ℝ} (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0)
    {z : ℂ} (hz : z ∈ contractingConjugates x) : z ≠ 0 := by
  intro hzero
  have he := (mem_aroots.mp (mem_contractingConjugates.mp hz).1).2
  rw [hzero, aeval_def, eval₂_at_zero] at he
  exact integerMinimalPolynomial_coeff_zero_ne_zero hx hx0
    ((algebraMap ℤ ℂ).injective_int (by simpa using he))

/-- All conjugate moduli of a unit multiply to one, with multiplicity. -/
theorem prod_conjugate_norms_eq_one {x : ℝ} (hx : IsAlgebraicUnit x) :
    (((integerMinimalPolynomial x).aroots ℂ).map (fun z ↦ ‖z‖)).prod = 1 := by
  let P := (integerMinimalPolynomial x).map (Int.castRingHom ℂ)
  have hm : P.Monic := (integerMinimalPolynomial_monic_of_isIntegral hx.2.1).map _
  have hp := (IsAlgClosed.splits P).coeff_zero_eq_prod_roots_of_monic hm
  have hn := congrArg norm hp
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hn
  have hc : ‖P.coeff 0‖ = (1 : ℝ) := by
    simp only [P, coeff_map, Int.coe_castRingHom, Complex.norm_intCast]
    exact_mod_cast integerMinimalPolynomial_coeff_zero_abs_eq_one hx
  rw [hc] at hn
  change (P.roots.map (fun z ↦ ‖z‖)).prod = 1
  have hnorm := map_multiset_prod (normHom.toMonoidHom : ℂ →* ℝ) P.roots
  exact hnorm.symm.trans hn.symm

/-- The determinant modulus of the contracting-conjugate representation is
exactly the inverse canonical Mahler measure. -/
theorem prod_contractingConjugate_norms_eq_inv_mahlerMeasure {x : ℝ}
    (hx : IsAlgebraicUnit x) :
    ((contractingConjugates x).map (fun z ↦ ‖z‖)).prod = (mahlerMeasure x)⁻¹ := by
  classical
  have ha : IsAlgebraic ℚ x := (hx.2.1.tower_top (A := ℚ)).isAlgebraic
  let R := (integerMinimalPolynomial x).aroots ℂ
  let inside := R.filter (fun z ↦ ‖z‖ < 1)
  let outside := R.filter (fun z ↦ ¬‖z‖ < 1)
  have hsplit : inside + outside = R := Multiset.filter_add_not _ _
  have hout : (outside.map (fun z ↦ max 1 ‖z‖)).prod =
      (outside.map (fun z ↦ ‖z‖)).prod := by
    congr 1
    apply Multiset.map_congr rfl
    intro z hz
    exact max_eq_right (le_of_not_gt (Multiset.mem_filter.mp hz).2)
  have hin : (inside.map (fun z ↦ max 1 ‖z‖)).prod = 1 := by
    apply Multiset.prod_eq_one
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
    exact max_eq_left (Multiset.mem_filter.mp hz).2.le
  have hM : mahlerMeasure x = (outside.map (fun z ↦ ‖z‖)).prod := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_aroots ha,
      (integerMinimalPolynomial_monic_of_isIntegral hx.2.1).leadingCoeff]
    simp only [Int.cast_one, one_mul]
    change (R.map (fun z ↦ max 1 ‖z‖)).prod = _
    rw [← hsplit, Multiset.map_add, Multiset.prod_add, hin, one_mul, hout]
  have hprod : (inside.map (fun z ↦ ‖z‖)).prod *
      (outside.map (fun z ↦ ‖z‖)).prod = 1 := by
    rw [← Multiset.prod_add, ← Multiset.map_add, hsplit]
    exact prod_conjugate_norms_eq_one hx
  change (inside.map (fun z ↦ ‖z‖)).prod = _
  rw [hM]
  exact eq_inv_of_mul_eq_one_left hprod

end LpSelfSimilar.Algebraic
