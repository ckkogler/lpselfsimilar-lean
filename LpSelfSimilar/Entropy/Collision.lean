module

public import LpSelfSimilar.Entropy.Bounds
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
Finite entropy is controlled by the probability that two independent samples
disagree. The five-atom case supplies the elementary entropy estimate used
inside a coarse grid cell in Lemma 3.5.
-/

open Real Set
open scoped ENNReal

namespace LpSelfSimilar.Entropy

lemma two_mul_log_le_self {u : ℝ} (hu : 0 < u) : 2 * Real.log u ≤ u := by
  have h := Real.log_le_sub_one_of_pos (by positivity : 0 < u / 2)
  rw [Real.log_div hu.ne' (by norm_num)] at h
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

lemma log_sq_le_sub_one {u : ℝ} (hu : 1 ≤ u) : (Real.log u) ^ 2 ≤ u - 1 := by
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun t ↦ t - 1 - (Real.log t) ^ 2)
        (1 - 2 * Real.log x / x) x := by
    convert ((hasDerivAt_id x).sub_const 1).sub ((Real.hasDerivAt_log hx.ne').pow 2)
      using 1 <;> try rfl
    simp only [Nat.cast_ofNat, pow_one, Nat.reduceSub]
    ring
  have hm : MonotoneOn (fun x ↦ x - 1 - (Real.log x) ^ 2) (Ioi 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
    · exact fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact (hd x hx).hasDerivWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      have h := two_mul_log_le_self hx
      have := (div_le_one hx).mpr h
      linarith
  have h := hm (by norm_num : (1 : ℝ) ∈ Ioi 0) (by change 0 < u; linarith) hu
  simp only [Real.log_one, zero_pow (by decide : 2 ≠ 0)] at h
  linarith

lemma negMulLog_sq_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (Real.negMulLog x) ^ 2 ≤ x - x ^ 2 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · simp
  have hu : 1 ≤ x⁻¹ := (one_le_inv₀ hx).mpr hx1
  have h := mul_le_mul_of_nonneg_left (log_sq_le_sub_one hu) (sq_nonneg x)
  rw [Real.log_inv] at h
  have heq : x ^ 2 * (x⁻¹ - 1) = x - x ^ 2 := by field_simp
  rw [heq] at h
  unfold Real.negMulLog
  nlinarith

/-- Probability that two independent samples from this finite law agree. -/
noncomputable def collisionProbability {α : Type*} (p : PMF α) (hp : p.support.Finite) : ℝ :=
  ∑ a ∈ hp.toFinset, (p a).toReal ^ 2

lemma collisionProbability_le_one {α : Type*} (p : PMF α) (hp : p.support.Finite) :
    collisionProbability p hp ≤ 1 := by
  rw [← sum_support_toReal p hp]
  apply Finset.sum_le_sum
  intro a _
  have hx : (p a).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using p.coe_le_one a)
  nlinarith [ENNReal.toReal_nonneg (a := p a)]

lemma finiteEntropy_sq_le_card_mul_disagreement {α : Type*}
    (p : PMF α) (hp : p.support.Finite) :
    (finiteEntropy p hp) ^ 2 ≤ hp.toFinset.card * (1 - collisionProbability p hp) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq hp.toFinset
    (fun a ↦ Real.negMulLog (p a).toReal) (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  apply h.trans
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    (∑ a ∈ hp.toFinset, (Real.negMulLog (p a).toReal) ^ 2) ≤
        ∑ a ∈ hp.toFinset, ((p a).toReal - (p a).toReal ^ 2) := by
      apply Finset.sum_le_sum
      intro a _
      exact negMulLog_sq_le ENNReal.toReal_nonneg
        (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using p.coe_le_one a))
    _ = _ := by rw [Finset.sum_sub_distrib, sum_support_toReal]; rfl

/-- The five-cell entropy bound used in the entropy-to-variance argument. -/
lemma finiteEntropy_le_four_sqrt_disagreement {α : Type*}
    (p : PMF α) (hp : p.support.Finite) (hcard : hp.toFinset.card ≤ 5) :
    finiteEntropy p hp ≤ 4 * Real.sqrt (1 - collisionProbability p hp) := by
  have hd : 0 ≤ 1 - collisionProbability p hp := sub_nonneg.mpr (collisionProbability_le_one p hp)
  have hs := Real.sq_sqrt hd
  have h := finiteEntropy_sq_le_card_mul_disagreement p hp
  have hc : (hp.toFinset.card : ℝ) ≤ 5 := by exact_mod_cast hcard
  have hm := mul_le_mul_of_nonneg_right hc hd
  nlinarith [Real.sqrt_nonneg (1 - collisionProbability p hp)]

end LpSelfSimilar.Entropy
