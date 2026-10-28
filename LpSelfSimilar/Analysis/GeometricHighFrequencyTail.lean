module

public import LpSelfSimilar.Analysis.GeometricBandShift

@[expose] public section

/-!
# Selecting a small-angle tail at an arbitrary high frequency

A geometric sequence starting at or above one enters the closed band
[1, 1/theta] at a natural index. The initial index handles the band itself;
otherwise the proved logarithmic ceiling is nonnegative. Both endpoints are
retained, so the result also applies at the low/high frequency boundary.
-/

namespace LpSelfSimilar.Analysis

/-- Every high initial angle admits a natural tail whose first angle is in the target band. -/
theorem exists_nat_geometric_angle_band {θ A : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 1 ≤ A) :
    ∃ n : ℕ, 1 ≤ θ ^ n * A ∧ θ ^ n * A ≤ 1 / θ := by
  by_cases hband : A ≤ 1 / θ
  · exact ⟨0, by simpa using hA, by simpa using hband⟩
  · have hb : 0 < 1 / θ := by positivity
    have hn : 0 ≤ geometricBandShift θ A (1 / θ) :=
      geometricBandShift_nonneg hθ0 hθ1 hb (le_of_not_ge hband)
    have hs := geometricBandShift_spec hθ0 hθ1 (by linarith : 0 < A) hb
    have hc : ((geometricBandShift θ A (1 / θ)).toNat : ℤ) =
        geometricBandShift θ A (1 / θ) := Int.toNat_of_nonneg hn
    rw [← hc, zpow_natCast] at hs
    have he : θ * (1 / θ) = 1 := by field_simp
    rw [he] at hs
    exact ⟨_, hs.1.le, hs.2⟩

end LpSelfSimilar.Analysis
