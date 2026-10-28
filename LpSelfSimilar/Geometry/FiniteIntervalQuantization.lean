module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic

@[expose] public section

/-!
# Finite quantization of points in a real interval

Shifting the interval's left endpoint to zero and taking the natural floor gives
half-open cells of length `a`. Points in the same cell are strictly closer than
`a`, and at most `(hi-lo)/a+1` cells are needed, including interval endpoints.
-/

namespace LpSelfSimilar.Geometry

/-- An actual finite cell label with strict within-cell diameter and explicit cell count. -/
theorem exists_finite_interval_quantization {ι : Type*} (z : ι → ℝ)
    (lo hi a : ℝ) (hlohi : lo ≤ hi) (ha : 0 < a)
    (hz : ∀ i, z i ∈ Set.Icc lo hi) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ (hi - lo) / a + 1 ∧
      ∃ label : ι → Fin N, ∀ i j, label i = label j → |z i - z j| < a := by
  let N := ⌊(hi - lo) / a⌋₊ + 1
  let f : ι → ℕ := fun i ↦ ⌊(z i - lo) / a⌋₊
  have hn (i : ι) : 0 ≤ (z i - lo) / a := div_nonneg (sub_nonneg.mpr (hz i).1) ha.le
  have hbound (i : ι) : f i < N := by
    apply Nat.lt_succ_of_le
    apply Nat.floor_mono
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hz i).2 lo) ha.le
  refine ⟨N, Nat.succ_pos _, ?_, fun i ↦ ⟨f i, hbound i⟩, ?_⟩
  · dsimp [N]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le (div_nonneg (sub_nonneg.mpr hlohi) ha.le)]
  · intro i j he
    have hf : f i = f j := congrArg Fin.val he
    have hilow : (f i : ℝ) * a ≤ z i - lo := (le_div_iff₀ ha).mp (Nat.floor_le (hn i))
    have hiup : z i - lo < ((f i : ℝ) + 1) * a :=
      (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one ((z i - lo) / a))
    have hjlow : (f j : ℝ) * a ≤ z j - lo := (le_div_iff₀ ha).mp (Nat.floor_le (hn j))
    have hjup : z j - lo < ((f j : ℝ) + 1) * a :=
      (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one ((z j - lo) / a))
    rw [hf] at hilow hiup
    exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩

end LpSelfSimilar.Geometry
