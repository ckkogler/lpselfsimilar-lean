module

public import LpSelfSimilar.Fourier.QuinticCutoff
public import LpSelfSimilar.Analysis.ClampedQuinticValues

@[expose] public section

/-!
# Exact support and plateau of the even Fourier cutoff

The positive and negative transitions have disjoint interiors for widths at
most one. The two-transition definition therefore agrees with the specified
constant plateau, quintic transition, and zero exterior.
-/

open Set
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- Positive band membership is equivalent to unit transition-coordinate membership. -/
theorem quinticBandCoordinate_mem_Icc_iff {ε x : ℝ} (hε : 0 < ε) :
    quinticBandCoordinate ε x ∈ Icc 0 1 ↔ x ∈ Icc (1 - ε) (1 + ε) := by
  have h2 : 0 < 2 * ε := by positivity
  simp only [mem_Icc, quinticBandCoordinate]
  rw [le_div_iff₀ h2, div_le_iff₀ h2]
  constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith

/-- The affine coordinate is nonpositive precisely below the inner band endpoint. -/
theorem quinticBandCoordinate_nonpos_iff {ε x : ℝ} (hε : 0 < ε) :
    quinticBandCoordinate ε x ≤ 0 ↔ x ≤ 1 - ε := by
  unfold quinticBandCoordinate
  rw [div_le_iff₀ (by positivity : 0 < 2 * ε)]
  constructor <;> intro h <;> linarith

/-- The affine coordinate is at least one precisely beyond the outer endpoint. -/
theorem one_le_quinticBandCoordinate_iff {ε x : ℝ} (hε : 0 < ε) :
    1 ≤ quinticBandCoordinate ε x ↔ 1 + ε ≤ x := by
  unfold quinticBandCoordinate
  rw [le_div_iff₀ (by positivity : 0 < 2 * ε)]
  constructor <;> intro h <;> linarith

/-- The Fourier cutoff is exactly one throughout its closed central plateau. -/
theorem quinticFourierCutoff_eq_one {ε x : ℝ} (hε : 0 < ε)
    (hx : |x| ≤ 1 - ε) : quinticFourierCutoff ε x = 1 := by
  have h := abs_le.mp hx
  unfold quinticFourierCutoff
  rw [clampedQuintic_of_nonpos ((quinticBandCoordinate_nonpos_iff hε).mpr h.2),
    clampedQuintic_of_nonpos ((quinticBandCoordinate_nonpos_iff hε).mpr (by linarith [h.1]))]
  norm_num

/-- The cutoff vanishes at and beyond the outer transition endpoints. -/
theorem quinticFourierCutoff_eq_zero {ε x : ℝ} (hε : 0 < ε)
    (hx : 1 + ε ≤ |x|) : quinticFourierCutoff ε x = 0 := by
  have hpos (y : ℝ) (hy : 1 + ε ≤ y) : quinticFourierCutoff ε y = 0 := by
    unfold quinticFourierCutoff
    rw [clampedQuintic_of_one_le ((one_le_quinticBandCoordinate_iff hε).mpr hy),
      clampedQuintic_of_nonpos ((quinticBandCoordinate_nonpos_iff hε).mpr (by linarith))]
    norm_num
  rcases le_abs.mp hx with h | h
  · exact hpos x h
  · rw [← quinticFourierCutoff_neg ε x]
    exact hpos (-x) h

/-- On the positive closed band the even cutoff is exactly the prescribed quintic. -/
theorem quinticFourierCutoff_eq_transition {ε x : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hx : x ∈ Icc (1 - ε) (1 + ε)) :
    quinticFourierCutoff ε x = quinticTransition (quinticBandCoordinate ε x) := by
  unfold quinticFourierCutoff
  rw [clampedQuintic_eq_of_mem_Icc ((quinticBandCoordinate_mem_Icc_iff hε).mpr hx),
    clampedQuintic_of_nonpos ((quinticBandCoordinate_nonpos_iff hε).mpr (by linarith [hx.1]))]
  ring

/-- The cutoff has compact support, derived from its exact exterior values. -/
theorem hasCompactSupport_quinticFourierCutoff {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (quinticFourierCutoff ε) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-(1 + ε)) (1 + ε)))
  intro x hx
  apply quinticFourierCutoff_eq_zero hε
  by_contra h
  have ha := abs_lt.mp (lt_of_not_ge h)
  exact hx ⟨ha.1.le, ha.2.le⟩

end LpSelfSimilar.Fourier
