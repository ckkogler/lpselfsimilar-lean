module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section

/-!
# Cardinality of a finite separated set in a short interval

After shifting the leftmost position to zero, put each point into a half-open
cell of length `a`. Separation makes the cell map injective. A strict diameter
bound of `N * a` puts every cell index below `N`, including the endpoint case
needed for the sixteen-point distance-band argument.
-/

open Set

namespace LpSelfSimilar.Geometry

/-- An `a`-separated finite family of diameter strictly below `N*a` has at most `N` points. -/
theorem card_le_of_separated_strict_diameter {ι : Type*} (s : Finset ι)
    (z : ι → ℝ) (a : ℝ) (ha : 0 < a) (N : ℕ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → a ≤ |z i - z j|)
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, |z i - z j| < N * a) : s.card ≤ N := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨m, hm, hmin⟩ := s.exists_min_image z hs
  let f : ι → ℕ := fun i ↦ ⌊(z i - z m) / a⌋₊
  have hnonneg (i : ι) (hi : i ∈ s) : 0 ≤ (z i - z m) / a :=
    div_nonneg (sub_nonneg.mpr (hmin i hi)) ha.le
  have hmaps : Set.MapsTo f (s : Set ι) (Finset.range N : Set ℕ) := by
    intro i hi
    apply Finset.mem_range.mpr
    apply (Nat.floor_lt (hnonneg i hi)).mpr
    apply (div_lt_iff₀ ha).mpr
    exact (le_abs_self (z i - z m)).trans_lt (hdiam i hi m hm)
  have hinj : Set.InjOn f (s : Set ι) := by
    intro i hi j hj he
    by_contra hij
    have hilow : (f i : ℝ) * a ≤ z i - z m :=
      (le_div_iff₀ ha).mp (Nat.floor_le (hnonneg i hi))
    have hiup : z i - z m < ((f i : ℝ) + 1) * a :=
      (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one ((z i - z m) / a))
    have hjlow : (f j : ℝ) * a ≤ z j - z m :=
      (le_div_iff₀ ha).mp (Nat.floor_le (hnonneg j hj))
    have hjup : z j - z m < ((f j : ℝ) + 1) * a :=
      (div_lt_iff₀ ha).mp (Nat.lt_floor_add_one ((z j - z m) / a))
    rw [he] at hilow hiup
    have hclose : |z i - z j| < a := abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
    exact (not_lt_of_ge (hsep i hi j hj hij)) hclose
  simpa using Finset.card_le_card_of_injOn f hmaps hinj

end LpSelfSimilar.Geometry
