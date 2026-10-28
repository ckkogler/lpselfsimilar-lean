module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

/-!
The explicit large-complexity observation used in the proof of Theorem 1.2.
Concavity supplies a uniform lower bound on 100 log B-B throughout [3,600].
The endpoint estimates use proved numerical bounds for natural logarithms.
-/

open Real Set

namespace LpSelfSimilar

lemma log_power_gap_ge_ten {B : ℝ} (hB : B ∈ Icc (3 : ℝ) 600) :
    10 ≤ 100 * log B - B := by
  have h3 : 1 ≤ log (3 : ℝ) := by linarith [log_three_gt_d9]
  have h600 : 61 / 10 ≤ log (600 : ℝ) := by
    have h := log_le_log (by norm_num : (0 : ℝ) < 2 ^ 9)
      (by norm_num : (2 : ℝ) ^ 9 ≤ 600)
    rw [log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [log_two_gt_d9]
  let a := (600 - B) / 597
  let b := (B - 3) / 597
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hB.2) (by norm_num)
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hB.1) (by norm_num)
  have hab : a + b = 1 := by dsimp [a, b]; ring
  have hmean : a * 3 + b * 600 = B := by dsimp [a, b]; ring
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show (3 : ℝ) ∈ Ioi 0 by norm_num) (show (600 : ℝ) ∈ Ioi 0 by norm_num)
    ha hb hab
  simp only [smul_eq_mul] at hc
  rw [hmean] at hc
  have h1 := mul_le_mul_of_nonneg_left h3 ha
  have h2 := mul_le_mul_of_nonneg_left h600 hb
  nlinarith

/-- The source's B>600 conclusion, with abstract positive gap and exact power 100. -/
theorem six_hundred_lt_of_small_gap {B g : ℝ} (hB : 3 ≤ B) (hg : 0 < g)
    (hlog : log (1 / g) ≤ B) (hsmall : g * B ^ 100 < 2) : 600 < B := by
  have hB0 : 0 < B := by linarith
  have hp := log_lt_log (by positivity : 0 < g * B ^ 100) hsmall
  rw [log_mul hg.ne' (pow_pos hB0 100).ne', log_pow] at hp
  rw [one_div, log_inv] at hlog
  by_contra! hle
  have hlo := log_power_gap_ge_ten ⟨hB, hle⟩
  norm_num only [Nat.cast_ofNat] at hp
  linarith [log_two_lt_d9]

/-- The explicit power-selection loss is absorbed by exponent 100. -/
lemma gap_power_twenty_one_bound {B g : ℝ} (hB : 600 ≤ B) (hg : 0 ≤ g)
    (hsmall : g * B ^ 100 < 2) :
    g * B ^ 21 ≤ (1 / (10 : ℝ) ^ 100) / (2 * 101 ^ 11) := by
  have hB0 : 0 ≤ B := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 600) hB 79
  have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg hg (pow_nonneg hB0 21))
  have he : g * B ^ 21 * B ^ 79 = g * B ^ 100 := by ring
  rw [he] at hm
  have hbound : g * B ^ 21 ≤ 2 / (600 : ℝ) ^ 79 :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 600 ^ 79)).mpr (hm.trans hsmall.le)
  exact hbound.trans (by norm_num)

end LpSelfSimilar
