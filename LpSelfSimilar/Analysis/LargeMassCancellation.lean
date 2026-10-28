module

public import LpSelfSimilar.Analysis.CancellationProfile

@[expose] public section

/-!
# Cancellation when the mass outside a largest atom is at least one half

Rationalizing 1-sqrt(1-gamma*delta) gives the exact expression used in the
large-delta part of the finite entropy proof. Positivity and the endpoints are
explicit. The resulting coefficient is the same exact chord coefficient as
in the small-delta argument, and is strictly greater than 13/40.
-/

open Real Set

namespace LpSelfSimilar.Analysis

/-- Exact rationalization, with the radicand and division hypotheses discharged explicitly. -/
theorem one_sub_sqrt_div_eq {a x : ℝ} (hx : x ≠ 0) (hax : a * x ≤ 1) :
    (1 - sqrt (1 - a * x)) / x = a / (1 + sqrt (1 - a * x)) := by
  apply (div_eq_div_iff hx (by positivity : 1 + sqrt (1 - a * x) ≠ 0)).mpr
  nlinarith [Real.sq_sqrt (sub_nonneg.mpr hax)]

/-- The large-mass rationalized ratio is bounded below by the exact small-mass chord coefficient. -/
theorem large_mass_cancellation_ratio_lower {x : ℝ} (hx : x ∈ Icc (1 / 2) 1) :
    2 * (1 - sqrt (7 / 10)) ≤ (3 / 5) / (1 + sqrt (1 - (3 / 5) * x)) := by
  have he : (3 / 5 : ℝ) / (1 + sqrt (7 / 10)) = 2 * (1 - sqrt (7 / 10)) := by
    apply (div_eq_iff (by positivity)).mpr
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 10)]
  rw [← he]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have hs : sqrt (1 - (3 / 5) * x) ≤ sqrt (7 / 10) :=
    Real.sqrt_le_sqrt (by linarith [hx.1])
  linarith

/-- The displayed large-mass ratio identity and its exact chord bound. -/
theorem large_mass_cancellation_ratio {x : ℝ} (hx : x ∈ Icc (1 / 2) 1) :
    (1 - sqrt (1 - (3 / 5) * x)) / x = (3 / 5) / (1 + sqrt (1 - (3 / 5) * x)) ∧
      2 * (1 - sqrt (7 / 10)) ≤ (1 - sqrt (1 - (3 / 5) * x)) / x := by
  have he := one_sub_sqrt_div_eq (a := 3 / 5) (x := x) (by linarith [hx.1])
    (by linarith [hx.2])
  exact ⟨he, he ▸ large_mass_cancellation_ratio_lower hx⟩

/-- The exact 13/40 coefficient follows in the entire large-mass range. -/
theorem large_mass_cancellation_thirteen_fortieths {x : ℝ} (hx : x ∈ Icc (1 / 2) 1) :
    (13 / 40 : ℝ) * x < 1 - sqrt (1 - (3 / 5) * x) := by
  exact (lt_div_iff₀ (by linarith [hx.1] : 0 < x)).mp
    (cancellationProfile_chord_coefficient_gt.trans_le (large_mass_cancellation_ratio hx).2)

end LpSelfSimilar.Analysis
