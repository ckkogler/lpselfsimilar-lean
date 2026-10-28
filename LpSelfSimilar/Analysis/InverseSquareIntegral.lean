module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic

@[expose] public section

/-!
The elementary inverse-square tail integral, with positivity excluding the pole.
This is the integrable envelope for detail in logarithmic coordinates.
-/

open MeasureTheory Set

namespace LpSelfSimilar

lemma integral_inverse_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ R in a..b, 1 / R ^ 2) = 1 / a - 1 / b := by
  have hc : ContinuousOn (fun R : ℝ ↦ 1 / R ^ 2) (Icc a b) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro R hR
    exact pow_ne_zero _ (ha.trans_le hR.1).ne'
  have hd (R : ℝ) (hR : R ∈ Set.uIcc a b) :
      HasDerivAt (fun S : ℝ ↦ -(S⁻¹)) (1 / R ^ 2) R := by
    rw [uIcc_of_le hab] at hR
    convert ((hasDerivAt_id R).inv (ha.trans_le hR.1).ne').neg using 1 <;> try rfl
    simp only [id_eq, neg_div, neg_neg]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hc.intervalIntegrable_of_Icc hab)
  exact h.trans (by ring)

lemma integral_inverse_sq_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ R in a..b, 1 / R ^ 2) ≤ 1 / a := by
  rw [integral_inverse_sq ha hab]
  have hb := ha.trans_le hab
  have h : 0 ≤ 1 / b := by positivity
  linarith

end LpSelfSimilar
