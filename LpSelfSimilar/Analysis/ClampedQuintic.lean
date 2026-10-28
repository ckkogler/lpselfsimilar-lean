module

public import LpSelfSimilar.Analysis.QuinticTransition
public import LpSelfSimilar.Analysis.DerivativeGluing
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section

/-!
# The globally clamped quintic transition

The transition is extended by one to the left and zero to the right. Endpoint
matching proves its first two derivatives everywhere, including the joins.
Its second derivative is continuous; no claim is made about a third derivative
at the joins.
-/

open Set

namespace LpSelfSimilar.Analysis

/-- The quintic transition extended constantly outside the unit interval. -/
noncomputable def clampedQuintic (u : ℝ) : ℝ :=
  if u ≤ 0 then 1 else if u ≤ 1 then quinticTransition u else 0

/-- The first derivative of the clamped transition. -/
noncomputable def clampedQuinticSlope (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else if u ≤ 1 then quinticTransitionSlope u else 0

/-- The second derivative of the clamped transition. -/
noncomputable def clampedQuinticCurvature (u : ℝ) : ℝ :=
  if u ≤ 0 then 0 else if u ≤ 1 then quinticTransitionCurvature u else 0

/-- The explicit clamped slope is the actual derivative, including both joins. -/
theorem hasDerivAt_clampedQuintic (u : ℝ) :
    HasDerivAt clampedQuintic (clampedQuinticSlope u) u := by
  have hi := hasDerivAt_if_le (a := 1) (hasDerivAt_quinticTransition u)
    (hasDerivAt_const u (0 : ℝ))
    (by norm_num [quinticTransition])
    (by intro h; subst u; norm_num [quinticTransitionSlope])
  exact hasDerivAt_if_le (a := 0) (hasDerivAt_const u (1 : ℝ)) hi
    (by norm_num [quinticTransition])
    (by intro h; subst u; norm_num [quinticTransitionSlope])

/-- The explicit clamped curvature is the actual derivative of the clamped slope. -/
theorem hasDerivAt_clampedQuinticSlope (u : ℝ) :
    HasDerivAt clampedQuinticSlope (clampedQuinticCurvature u) u := by
  have hi := hasDerivAt_if_le (a := 1) (hasDerivAt_quinticTransitionSlope u)
    (hasDerivAt_const u (0 : ℝ))
    (by norm_num [quinticTransitionSlope])
    (by intro h; subst u; norm_num [quinticTransitionCurvature])
  exact hasDerivAt_if_le (a := 0) (hasDerivAt_const u (0 : ℝ)) hi
    (by norm_num [quinticTransitionSlope])
    (by intro h; subst u; norm_num [quinticTransitionCurvature])

/-- The clamped curvature is continuous, including both endpoints. -/
theorem continuous_clampedQuinticCurvature : Continuous clampedQuinticCurvature := by
  have hc : Continuous quinticTransitionCurvature := by unfold quinticTransitionCurvature; fun_prop
  have hi := hc.if_le (continuous_const (y := (0 : ℝ))) continuous_id (continuous_const (y := (1 : ℝ)))
    (by intro u h; change u = 1 at h; subst u; norm_num [quinticTransitionCurvature])
  exact (continuous_const (y := (0 : ℝ))).if_le hi continuous_id (continuous_const (y := (0 : ℝ)))
    (by intro u h; change u = 0 at h; subst u; norm_num [quinticTransitionCurvature])

/-- The clamped transition is exactly one to the left of the unit interval. -/
theorem clampedQuintic_of_nonpos {u : ℝ} (hu : u ≤ 0) : clampedQuintic u = 1 := by
  simp only [clampedQuintic, if_pos hu]

/-- The clamped transition is exactly zero to the right, including the endpoint. -/
theorem clampedQuintic_of_one_le {u : ℝ} (hu : 1 ≤ u) : clampedQuintic u = 0 := by
  rw [clampedQuintic, if_neg (by linarith)]
  by_cases h : u ≤ 1
  · have he : u = 1 := le_antisymm h hu
    norm_num [he, quinticTransition]
  · simp only [if_neg h]

/-- The clamped slope vanishes off the open transition interval. -/
theorem clampedQuinticSlope_eq_zero {u : ℝ} (hu : u ≤ 0 ∨ 1 ≤ u) :
    clampedQuinticSlope u = 0 := by
  rcases hu with h | h
  · simp only [clampedQuinticSlope, if_pos h]
  · rw [clampedQuinticSlope, if_neg (by linarith)]
    by_cases h' : u ≤ 1
    · have he : u = 1 := le_antisymm h' h
      simp [he, quinticTransitionSlope]
    · simp only [if_neg h']

/-- The clamped transition has values in the unit interval everywhere. -/
theorem clampedQuintic_mem_Icc (u : ℝ) : clampedQuintic u ∈ Icc 0 1 := by
  unfold clampedQuintic
  split_ifs with h0 h1
  · norm_num
  · exact quinticTransition_mem_Icc ⟨by linarith, h1⟩
  · norm_num

end LpSelfSimilar.Analysis
