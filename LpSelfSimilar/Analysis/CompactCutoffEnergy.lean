module

public import LpSelfSimilar.Analysis.SupportedIntervalIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic

@[expose] public section

/-!
# Squared energy of a continuous cutoff with bounded support

Continuity and the explicit support interval prove integrability. A cutoff
bounded in absolute value by one has squared energy at most the interval
length. The support endpoints are included, avoiding hidden boundary terms.
-/

open Set MeasureTheory

namespace LpSelfSimilar.Analysis

/-- A continuous real function vanishing beyond an absolute radius has integrable square. -/
theorem integrable_sq_of_continuous_zero_off_abs {q : ℝ → ℝ} {S : ℝ}
    (hq : Continuous q) (hz : ∀ x : ℝ, S ≤ |x| → q x = 0) :
    Integrable (fun x => q x ^ 2) := by
  apply (hq.pow 2).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-S) S))
  intro x hx
  have ho : S ≤ |x| := by
    by_contra h
    have ha := abs_lt.mp (lt_of_not_ge h)
    exact hx ⟨ha.1.le, ha.2.le⟩
  simp only [Pi.pow_apply, hz x ho, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

/-- The squared cutoff energy is at most the exact length of its support interval. -/
theorem integral_sq_cutoff_le_twice_radius {q : ℝ → ℝ} {S : ℝ}
    (hS : 0 ≤ S) (hq : Continuous q) (hb : ∀ x : ℝ, |q x| ≤ 1)
    (hz : ∀ x : ℝ, S ≤ |x| → q x = 0) :
    (∫ x : ℝ, q x ^ 2) ≤ 2 * S := by
  rw [integral_eq_interval_of_eq_zero_off_Ioo (a := -S) (b := S) (fun x hx => by
    have ha : S ≤ |x| := by
      rcases hx with hx | hx
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl hx)
    rw [hz x ha]
    norm_num)]
  have hi : IntervalIntegrable (fun x => q x ^ 2) volume (-S) S :=
    (hq.pow 2).intervalIntegrable (-S) S
  have hm := intervalIntegral.integral_mono_on (by linarith : -S ≤ S) hi
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (-S) S)
    (fun x hx => by nlinarith [sq_abs (q x), hb x, abs_nonneg (q x)])
  simpa [two_mul] using hm

end LpSelfSimilar.Analysis
