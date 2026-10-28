module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic

@[expose] public section

/-!
# The exact finite cutoff for geometric block lengths

For a multiplier `N>1` and a ratio `Q>=1`, the count `1+floor(log(Q)/log(N))`
selects exactly the natural exponents whose powers do not exceed `Q`.
Nonnegativity of the logarithmic quotient justifies the use of the natural floor
and its agreement with the integer-floor formula.
-/

namespace LpSelfSimilar.Analysis

/-- Number of nonnegative geometric exponents up to the given positive ratio. -/
noncomputable def geometricLengthCount (N Q : ℝ) : ℕ :=
  1 + ⌊Real.log Q / Real.log N⌋₊

/-- The cutoff always includes an initial exponent. -/
theorem geometricLengthCount_pos (N Q : ℝ) : 0 < geometricLengthCount N Q := by
  unfold geometricLengthCount
  omega

/-- On the intended domain the natural count is exactly the source's integer-floor formula. -/
theorem geometricLengthCount_intCast {N Q : ℝ} (hN : 1 < N) (hQ : 1 ≤ Q) :
    (geometricLengthCount N Q : ℤ) = 1 + ⌊Real.log Q / Real.log N⌋ := by
  have hq : 0 ≤ Real.log Q / Real.log N :=
    div_nonneg (Real.log_nonneg hQ) (Real.log_pos hN).le
  simp only [geometricLengthCount, Nat.cast_add, Nat.cast_one, Int.natCast_floor_eq_floor hq]

/-- The cutoff selects exactly the powers no greater than the given ratio. -/
theorem lt_geometricLengthCount_iff {N Q : ℝ} (hN : 1 < N) (hQ : 1 ≤ Q) (k : ℕ) :
    k < geometricLengthCount N Q ↔ N ^ k ≤ Q := by
  have hN0 : 0 < N := by linarith
  have hQ0 : 0 < Q := by linarith
  have hlog := Real.log_pos hN
  have hq : 0 ≤ Real.log Q / Real.log N := div_nonneg (Real.log_nonneg hQ) hlog.le
  rw [geometricLengthCount, Nat.add_comm, Nat.lt_add_one_iff, Nat.le_floor_iff hq,
    le_div_iff₀ hlog, ← Real.log_pow]
  exact Real.log_le_log_iff (pow_pos hN0 _) hQ0

/-- The first excluded power is strictly beyond the ratio, including exact-power endpoints. -/
theorem ratio_lt_pow_geometricLengthCount {N Q : ℝ} (hN : 1 < N) (hQ : 1 ≤ Q) :
    Q < N ^ geometricLengthCount N Q := by
  by_contra h
  have hk := (lt_geometricLengthCount_iff hN hQ (geometricLengthCount N Q)).mpr (le_of_not_gt h)
  exact (lt_irrefl _) hk

end LpSelfSimilar.Analysis
