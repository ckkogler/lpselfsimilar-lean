module

public import LpSelfSimilar.Analysis.CubicThresholdNumerics
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# The exact integer threshold for the cubic rational sufficient condition

The allowance F(x)=x/(2+log(x))^3 has the displayed derivative and is strictly
increasing for x>=3. Certified values at 587 and 588, together with the small
integer cases, prove that F(n)>=1 holds exactly for natural n>=588. This is
an exact threshold for the sufficient condition, not a necessity claim for
continuity of a Bernoulli convolution density.
-/

open Real Set

namespace LpSelfSimilar.Analysis

/-- The largest numerator allowed by the rational cubic condition at a real denominator. -/
noncomputable def cubicRationalAllowance (x : ℝ) : ℝ := x / (2 + log x) ^ 3

/-- Exact derivative, before imposing the positive range. -/
theorem hasDerivAt_cubicRationalAllowance {x : ℝ} (hx : x ≠ 0) (hden : 2 + log x ≠ 0) :
    HasDerivAt cubicRationalAllowance ((log x - 1) / (2 + log x) ^ 4) x := by
  convert! (hasDerivAt_id x).div (((hasDerivAt_log hx).const_add 2).pow 3)
    (pow_ne_zero 3 hden) using 1 <;> simp only [cubicRationalAllowance, id_eq, Pi.pow_apply] <;> field_simp <;> ring

/-- The rational allowance increases strictly throughout the relevant denominator range. -/
theorem strictMonoOn_cubicRationalAllowance : StrictMonoOn cubicRationalAllowance (Ici 3) := by
  have hp (x : ℝ) (hx : x ∈ Ici 3) : 0 < x := by have h : 3 ≤ x := hx; linarith
  have hl (x : ℝ) (hx : x ∈ Ici 3) : 1 < log x := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 3) hx
    linarith [log_three_gt_d9]
  have hd (x : ℝ) (hx : x ∈ Ici 3) : 0 < 2 + log x := by linarith [hl x hx]
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 3)
    (fun x hx => (hasDerivAt_cubicRationalAllowance (hp x hx).ne' (hd x hx).ne').continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_cubicRationalAllowance
      (hp x (interior_subset hx)).ne' (hd x (interior_subset hx)).ne').hasDerivWithinAt)
  intro x hx
  exact div_pos (sub_pos.mpr (hl x (interior_subset hx))) (pow_pos (hd x (interior_subset hx)) 4)

/-- The sufficient inequality fails at 587. -/
theorem cubicRationalAllowance_587_lt_one : cubicRationalAllowance 587 < 1 := by
  apply (div_lt_one (by positivity : (0 : ℝ) < (2 + log 587) ^ 3)).mpr
  linarith [cubic_denominator_587_gt]

/-- The sufficient inequality holds strictly at 588. -/
theorem one_lt_cubicRationalAllowance_588 : 1 < cubicRationalAllowance 588 := by
  apply (one_lt_div (by positivity : (0 : ℝ) < (2 + log 588) ^ 3)).mpr
  linarith [cubic_denominator_588_lt]

/-- Small denominators fail the sufficient condition as well, including the totalized value at zero. -/
theorem cubicRationalAllowance_nat_lt_one_of_le_two {n : ℕ} (hn : n ≤ 2) :
    cubicRationalAllowance n < 1 := by
  have hl : 0 ≤ log (n : ℝ) := by
    by_cases hzero : n = 0
    · simp [hzero]
    · exact log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzero)
  have hden : 0 < 2 + log (n : ℝ) := by linarith
  apply (div_lt_one (pow_pos hden 3)).mpr
  have hn2 : (n : ℝ) ≤ 2 := by exact_mod_cast hn
  have hc : (8 : ℝ) ≤ (2 + log (n : ℝ)) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (show 2 ≤ 2 + log (n : ℝ) by linarith) 3
    norm_num at h
    exact h
  linarith

/-- The cubic sufficient condition in the family 1-1/n holds exactly from n=588 onward. -/
theorem cubicRationalAllowance_integer_threshold (n : ℕ) :
    1 ≤ cubicRationalAllowance n ↔ 588 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hn587 : n ≤ 587 := by omega
    by_cases hn3 : 3 ≤ n
    · have hm := strictMonoOn_cubicRationalAllowance.monotoneOn
        (show (n : ℝ) ∈ Ici 3 from by change (3 : ℝ) ≤ (n : ℝ); exact_mod_cast hn3)
        (show (587 : ℝ) ∈ Ici 3 from by norm_num) (by exact_mod_cast hn587)
      linarith [cubicRationalAllowance_587_lt_one]
    · exact (cubicRationalAllowance_nat_lt_one_of_le_two (by omega)).not_ge h
  · intro hn
    have hm := strictMonoOn_cubicRationalAllowance.monotoneOn
      (show (588 : ℝ) ∈ Ici 3 from by norm_num)
      (show (n : ℝ) ∈ Ici 3 from by change (3 : ℝ) ≤ (n : ℝ); exact_mod_cast (show 3 ≤ n by omega))
      (by exact_mod_cast hn)
    exact one_lt_cubicRationalAllowance_588.le.trans hm

end LpSelfSimilar.Analysis
