module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# A fixed decreasing positive sequence of scales

Starting at chi, the scale chi/(n+1) decreases to zero. Keeping this sequence
explicit avoids choices in the eventual density construction and its error
comparison with the initial smoothing.
-/

open Filter
open scoped Topology

namespace LpSelfSimilar.Analysis

/-- A fixed sequence of positive scales when the initial scale is positive. -/
noncomputable def reciprocalScaleSequence (χ : ℝ) (n : ℕ) : ℝ := χ / ((n : ℝ) + 1)

/-- The sequence begins at its prescribed initial scale. -/
theorem reciprocalScaleSequence_zero (χ : ℝ) : reciprocalScaleSequence χ 0 = χ := by
  simp [reciprocalScaleSequence]

/-- Every term is positive when the initial scale is positive. -/
theorem reciprocalScaleSequence_pos {χ : ℝ} (hχ : 0 < χ) (n : ℕ) :
    0 < reciprocalScaleSequence χ n := by
  unfold reciprocalScaleSequence
  positivity

/-- A nonnegative initial scale gives a decreasing sequence. -/
theorem antitone_reciprocalScaleSequence {χ : ℝ} (hχ : 0 ≤ χ) :
    Antitone (reciprocalScaleSequence χ) := by
  intro n m hnm
  apply div_le_div_of_nonneg_left hχ (by positivity)
  have hnmR : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  linarith

/-- The explicit reciprocal scale sequence tends to zero. -/
theorem tendsto_reciprocalScaleSequence (χ : ℝ) :
    Tendsto (reciprocalScaleSequence χ) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => χ / ((n : ℝ) + 1)) atTop (𝓝 0)
  simpa only [mul_one_div, mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul χ

end LpSelfSimilar.Analysis
