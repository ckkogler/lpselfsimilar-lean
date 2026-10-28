module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-!
# The exponent of a contracting mass recurrence

The exact logarithmic exponent converts a geometric mass factor beta into a
power of the volume scale D. The inequalities here identify its range and the
sharp quadratic-moment threshold without an approximate exponent.
-/

open Real

namespace LpSelfSimilar.Analysis

/-- The power exponent associated to a mass factor beta and a volume multiplier D. -/
noncomputable def massDecayExponent (β D : ℝ) : ℝ := log (1 / β) / log D

/-- A strictly contracting mass factor gives a positive exponent. -/
theorem massDecayExponent_pos {β D : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hD : 1 < D) :
    0 < massDecayExponent β D := by
  exact div_pos (log_pos ((lt_div_iff₀ hβ).mpr (by simpa using hβ1))) (log_pos hD)

/-- The exponent is below one precisely when the volume gain dominates the mass loss. -/
theorem massDecayExponent_lt_one_iff {β D : ℝ} (hβ : 0 < β) (hD : 1 < D) :
    massDecayExponent β D < 1 ↔ 1 < β * D := by
  rw [massDecayExponent, div_lt_one (log_pos hD),
    log_lt_log_iff (one_div_pos.mpr hβ) (zero_lt_one.trans hD), div_lt_iff₀ hβ, mul_comm]

/-- The exponent exceeds one half precisely at the sharp quadratic mass threshold. -/
theorem half_lt_massDecayExponent_iff {β D : ℝ} (hβ : 0 < β) (hD : 1 < D) :
    (1 / 2 : ℝ) < massDecayExponent β D ↔ β ^ 2 * D < 1 := by
  have hlog : log (β ^ 2 * D) = 2 * log β + log D := by
    rw [log_mul (pow_pos hβ _).ne' (zero_lt_one.trans hD).ne', log_pow]
    norm_num
  have hsign : log (β ^ 2 * D) < 0 ↔ β ^ 2 * D < 1 :=
    log_neg_iff (mul_pos (pow_pos hβ _) (zero_lt_one.trans hD))
  rw [massDecayExponent, lt_div_iff₀ (log_pos hD)]
  rw [one_div β, log_inv]
  rw [← hsign, hlog]
  constructor <;> intro h <;> linarith

/-- Raising the volume multiplier to the exact exponent inverts the mass factor. -/
theorem rpow_massDecayExponent {β D : ℝ} (hβ : 0 < β) (hD : 1 < D) :
    D ^ massDecayExponent β D = 1 / β := by
  have hlogD : log D ≠ 0 := (log_pos hD).ne'
  have heq : log D * (log (1 / β) / log D) = log (1 / β) := by field_simp
  rw [rpow_def_of_pos (zero_lt_one.trans hD), massDecayExponent, heq,
    exp_log (one_div_pos.mpr hβ)]

/-- Exact geometric volumes have exact power masses. -/
theorem geometric_volume_rpow_massDecayExponent {R β D : ℝ}
    (hR : 0 ≤ R) (hβ : 0 < β) (hD : 1 < D) (n : ℕ) :
    (R / D ^ n) ^ massDecayExponent β D = R ^ massDecayExponent β D * β ^ n := by
  rw [div_rpow hR (pow_nonneg (zero_lt_one.trans hD).le _),
    ← rpow_pow_comm (zero_lt_one.trans hD).le, rpow_massDecayExponent hβ hD,
    one_div, inv_pow, div_inv_eq_mul]

end LpSelfSimilar.Analysis
