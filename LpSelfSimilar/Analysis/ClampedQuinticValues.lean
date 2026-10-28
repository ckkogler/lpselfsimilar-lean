module

public import LpSelfSimilar.Analysis.ClampedQuintic

@[expose] public section

/-!
# Values of the clamped transition on and off its active interval

Endpoint identities let closed-interval formulas agree with the constant
extensions. These facts are useful for proving exact support and integral laws.
-/

open Set

namespace LpSelfSimilar.Analysis

/-- The clamped transition agrees with its polynomial on the closed unit interval. -/
theorem clampedQuintic_eq_of_mem_Icc {u : ℝ} (hu : u ∈ Icc 0 1) :
    clampedQuintic u = quinticTransition u := by
  unfold clampedQuintic
  by_cases h : u ≤ 0
  · have he : u = 0 := le_antisymm h hu.1
    norm_num [he, quinticTransition]
  · simp only [if_neg h, if_pos hu.2]

/-- The clamped slope agrees with the polynomial slope at both endpoints too. -/
theorem clampedQuinticSlope_eq_of_mem_Icc {u : ℝ} (hu : u ∈ Icc 0 1) :
    clampedQuinticSlope u = quinticTransitionSlope u := by
  unfold clampedQuinticSlope
  by_cases h : u ≤ 0
  · have he : u = 0 := le_antisymm h hu.1
    norm_num [he, quinticTransitionSlope]
  · simp only [if_neg h, if_pos hu.2]

/-- The clamped curvature agrees with the polynomial curvature on the closed interval. -/
theorem clampedQuinticCurvature_eq_of_mem_Icc {u : ℝ} (hu : u ∈ Icc 0 1) :
    clampedQuinticCurvature u = quinticTransitionCurvature u := by
  unfold clampedQuinticCurvature
  by_cases h : u ≤ 0
  · have he : u = 0 := le_antisymm h hu.1
    norm_num [he, quinticTransitionCurvature]
  · simp only [if_neg h, if_pos hu.2]

/-- The clamped curvature vanishes off the open transition interval. -/
theorem clampedQuinticCurvature_eq_zero {u : ℝ} (hu : u ≤ 0 ∨ 1 ≤ u) :
    clampedQuinticCurvature u = 0 := by
  rcases hu with h | h
  · simp only [clampedQuinticCurvature, if_pos h]
  · rw [clampedQuinticCurvature, if_neg (by linarith)]
    by_cases h' : u ≤ 1
    · have he : u = 1 := le_antisymm h' h
      norm_num [he, quinticTransitionCurvature]
    · simp only [if_neg h']

end LpSelfSimilar.Analysis
