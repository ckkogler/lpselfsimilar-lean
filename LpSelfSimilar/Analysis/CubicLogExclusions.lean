module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic

@[expose] public section

/-!
# Logarithmic exclusions for the cubic complexity parameter

The cubic gap inequality forces a logarithmic graph below an affine graph.
Concavity and strictly positive endpoint values exclude the entire intervals
[3,8] and [3,11]. All endpoint certificates use proved logarithmic bounds;
the hypotheses may be non-strict, as required at the cubic endpoint.
-/

open Real Set

namespace LpSelfSimilar.Analysis

theorem concaveOn_three_log_sub_mul_add (a b : ℝ) :
    ConcaveOn ℝ (Ioi 0) (fun x : ℝ => 3 * log x - a * x + b) := by
  refine ⟨convex_Ioi _, ?_⟩
  intro x hx y hy u v hu hv huv
  have h := strictConcaveOn_log_Ioi.concaveOn.2 hx hy hu hv huv
  simp only [smul_eq_mul] at h ⊢
  have hb := congrArg (fun t : ℝ => t * b) huv
  nlinarith [hb]

/-- Concavity propagates strictly positive endpoint values across the closed interval. -/
theorem three_log_sub_mul_add_pos_on_Icc {a b l r x : ℝ}
    (hl : 0 < l) (hr : 0 < r) (hxl : l ≤ x) (hxr : x ≤ r)
    (hfl : 0 < 3 * log l - a * l + b) (hfr : 0 < 3 * log r - a * r + b) :
    0 < 3 * log x - a * x + b := by
  exact (lt_min hfl hfr).trans_le
    ((concaveOn_three_log_sub_mul_add a b).ge_on_segment hl hr (Icc_subset_segment ⟨hxl, hxr⟩))

theorem log_eight_eq_three_log_two : log (8 : ℝ) = 3 * log 2 := by
  have h := log_pow (2 : ℝ) 3
  norm_num at h
  exact h

/-- The first logarithmic constraint excludes even the endpoint B=8. -/
theorem eight_lt_of_cubic_log_constraint {B : ℝ} (hB : 3 ≤ B)
    (hlog : 3 * log B ≤ B - 2) : 8 < B := by
  by_contra h
  have hp := three_log_sub_mul_add_pos_on_Icc (a := 1) (b := 2)
    (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 8)
    hB (le_of_not_gt h)
    (by linarith [log_three_gt_d9])
    (by rw [log_eight_eq_three_log_two]; linarith [log_two_gt_d9])
  linarith

/-- A convenient lower certificate for log(11), using only small logarithms. -/
theorem five_log_two_sub_log_three_lt_log_eleven :
    5 * log 2 - log 3 < log (11 : ℝ) := by
  have h := log_lt_log (by norm_num : (0 : ℝ) < 32 / 3)
    (by norm_num : (32 / 3 : ℝ) < 11)
  have h32 : log (32 : ℝ) = 5 * log 2 := by
    have h := log_pow (2 : ℝ) 5
    norm_num at h
    exact h
  rwa [log_div (by norm_num) (by norm_num), h32] at h

/-- The sharper small-Mahler constraint excludes the full closed interval [3,11]. -/
theorem eleven_lt_of_cubic_log_constraint {B : ℝ} (hB : 3 ≤ B)
    (hlog : 3 * log B ≤ log 2 * B + 2 - 4 * log 2) : 11 < B := by
  by_contra h
  have hp := three_log_sub_mul_add_pos_on_Icc (a := log 2) (b := -2 + 4 * log 2)
    (by norm_num : (0 : ℝ) < 3) (by norm_num : (0 : ℝ) < 11)
    hB (le_of_not_gt h)
    (by linarith [log_three_gt_d9, log_two_gt_d9])
    (by linarith [five_log_two_sub_log_three_lt_log_eleven, log_two_gt_d9, log_three_lt_d9])
  linarith

end LpSelfSimilar.Analysis
