module

public import LpSelfSimilar.Bernoulli.FiniteBounds
public import LpSelfSimilar.Entropy.GridBounds
public import LpSelfSimilar.Entropy.LogScale

@[expose] public section

/-!
Coarse entropy of arbitrary real Bernoulli digit blocks from their proved
geometric support interval. The parameter need not be rational or algebraic.
This reusable bound supplies the coarse endpoint of the algebraic block-variance
argument. All logarithms are natural and the shift-uniform grid law is unchanged.
-/

open MeasureTheory Set Real
open LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

lemma digit_entropyOnLogScale_le_support {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hx : 0 ≤ x) (n : ℕ) :
    entropyOnLogScale (digitPMF r n) (digitPMF_support_finite _ _) x ≤
      x + Real.log 4 + Real.log ((1 - r)⁻¹) := by
  let K := (1 - r)⁻¹
  have hK : 0 < K := inv_pos.mpr (sub_pos.mpr hr1)
  have hK1 : 1 ≤ K := (one_le_inv₀ (sub_pos.mpr hr1)).mpr (by linarith)
  have he1 : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  have hbase := gridEntropy_le_log_length (digitPMF r n) (digitPMF_support_finite _ _)
    (digitPMF_support_subset_interval hr0 hr1 n) (Real.exp_pos (-x))
  change gridEntropy (digitPMF r n) _ (Real.exp (-x)) ≤ _
  apply hbase.trans
  have harg : ((1 - r)⁻¹ - -(1 - r)⁻¹) / Real.exp (-x) + 2 ≤
      4 * K * Real.exp x := by
    rw [Real.exp_neg, div_inv_eq_mul]
    dsimp only [K] at hK1 ⊢
    nlinarith [mul_le_mul hK1 he1 zero_le_one hK.le]
  calc
    _ ≤ Real.log (4 * K * Real.exp x) :=
      Real.log_le_log (by rw [sub_neg_eq_add]; positivity) harg
    _ = _ := by
      rw [Real.log_mul (by positivity : 4 * K ≠ 0) (Real.exp_ne_zero _),
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hK.ne', Real.log_exp]
      dsimp only [K]
      ring

end LpSelfSimilar.Bernoulli
