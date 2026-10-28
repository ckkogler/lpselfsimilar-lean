module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

/-!
# Binary decoder entropy and exact numerical margins

A binary error probability at most 1/32 has entropy at most
(1+log 32)/32. This bound and a rational exponential certificate retain the
strict 0.516 margin needed for a Gaussian information gain above one half.
-/

open Real Set

namespace LpSelfSimilar.Entropy

theorem binEntropy_one_div_thirty_two_le :
    binEntropy (1 / 32 : ℝ) ≤ (1 + log 32) / 32 := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  calc
    _ ≤ negMulLog (1 / 32) + (1 - (1 - 1 / 32)) :=
      add_le_add le_rfl (negMulLog_le_one_sub_self (by norm_num : (0 : ℝ) ≤ 1 - 1 / 32))
    _ = _ := by norm_num [negMulLog, log_div]; ring

/-- Small binary error has the precise entropy upper bound used by the decoder. -/
theorem binEntropy_le_of_le_one_div_thirty_two {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 32) :
    binEntropy p ≤ (1 + log 32) / 32 := by
  have h := binEntropy_strictMonoOn.monotoneOn
    (show p ∈ Icc 0 (2⁻¹ : ℝ) from ⟨hp0, hp.trans (by norm_num)⟩)
    (show (1 / 32 : ℝ) ∈ Icc 0 (2⁻¹ : ℝ) from by norm_num) hp
  exact h.trans binEntropy_one_div_thirty_two_le

/-- A positive finite Taylor sum certifies a convenient upper bound for exp(-4). -/
theorem exp_neg_four_lt : exp (-4) < (37 / 2000 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (4 : ℝ)) (by norm_num) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [exp_neg, ← one_div]
  apply (div_lt_iff₀ (exp_pos _)).mpr
  linarith

/-- Exact strict decimal margin; all logarithms are natural. -/
theorem binary_decoder_information_margin :
    (516 / 1000 : ℝ) < log 2 - (1 + log 32) / 32 - 2 * exp (-4) := by
  have hlog : log (32 : ℝ) = 5 * log 2 := by
    calc
      _ = log ((2 : ℝ) ^ 5) := by norm_num
      _ = _ := by rw [log_pow]; norm_num
  rw [hlog]
  linarith [exp_neg_four_lt, log_two_gt_d9]

end LpSelfSimilar.Entropy
