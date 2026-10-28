module

public import LpSelfSimilar.Algebraic.UnitPolynomial
public import LpSelfSimilar.Algebraic.Complexity

@[expose] public section

/-!
An elementary expanding-conjugate bound at the paper's complexity scale.

For an algebraic integer in (0,1), some conjugate has modulus greater than
exp(1/B). Otherwise the actual Mahler root product would give log M <= d/B,
contradicting B log M > d. This weaker, degree-dependent expansion is sufficient
for the exact entropy target length/(8B) after retaining sparse digits.
-/

open Polynomial

namespace LpSelfSimilar.Algebraic

lemma degree_lt_complexity_mul_log_mahlerMeasure {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (algebraicDegree x : ℝ) < complexity x * Real.log (mahlerMeasure x) := by
  have hB := complexity_pos hx hx0 hx1
  have hL := log_mahlerMeasure_pos hx hx0 hx1
  have hd := complexity_denominator_pos hx hx0 hx1
  have he : complexity x * min 1 (Real.log (mahlerMeasure x)) =
      1 + (algebraicDegree x : ℝ) + Real.log (mahlerMeasure x) := by
    rw [complexity, div_mul_cancel₀ _ hd.ne']
  have h := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (Real.log (mahlerMeasure x))) hB.le
  linarith

/-- An actual complex conjugate expands by more than exp(1/B). -/
theorem exists_expanding_conjugate {x : ℝ} (hx : IsIntegral ℤ x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ z ∈ (integerMinimalPolynomial x).aroots ℂ, Real.exp (1 / complexity x) < ‖z‖ := by
  have ha : IsAlgebraic ℚ x := (hx.tower_top (A := ℚ)).isAlgebraic
  have hB := complexity_pos ha hx0 hx1
  have hM := one_lt_mahlerMeasure ha hx0 hx1
  have hd := degree_lt_complexity_mul_log_mahlerMeasure ha hx0 hx1
  have hexp : 1 ≤ Real.exp (1 / complexity x) := Real.one_le_exp (by positivity)
  by_contra! h
  have hprod_aux (R : Multiset ℂ)
      (hR : ∀ z ∈ R, ‖z‖ ≤ Real.exp (1 / complexity x)) :
      (R.map (fun z ↦ max 1 ‖z‖)).prod ≤ Real.exp (1 / complexity x) ^ R.card := by
    induction R using Multiset.induction_on with
    | empty => simp
    | @cons z R ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
      apply mul_le_mul (max_le hexp (hR z (by simp)))
        (ih (fun w hw ↦ hR w (by simp [hw])))
      · apply Multiset.prod_nonneg
        intro y hy
        obtain ⟨w, _, rfl⟩ := Multiset.mem_map.mp hy
        exact le_trans zero_le_one (le_max_left _ _)
      · exact (Real.exp_pos _).le
  have hprod := hprod_aux ((integerMinimalPolynomial x).aroots ℂ) h
  have hcard : ((integerMinimalPolynomial x).aroots ℂ).card = algebraicDegree x := by
    rw [aroots, (IsAlgClosed.splits _).natDegree_eq_card_roots.symm,
      natDegree_map_eq_of_injective (algebraMap ℤ ℂ).injective_int,
      integerMinimalPolynomial_natDegree]
  rw [hcard] at hprod
  have hMp : mahlerMeasure x ≤ Real.exp (1 / complexity x) ^ algebraicDegree x := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_aroots ha,
      (integerMinimalPolynomial_monic_of_isIntegral hx).leadingCoeff]
    simpa using hprod
  have hl := Real.log_le_log (lt_trans zero_lt_one hM) hMp
  rw [Real.log_pow, Real.log_exp] at hl
  have hh := mul_le_mul_of_nonneg_left hl hB.le
  have he : complexity x * ((algebraicDegree x : ℝ) * (1 / complexity x)) = algebraicDegree x := by
    field_simp
  rw [he] at hh
  exact (not_le_of_gt hd) hh

end LpSelfSimilar.Algebraic
