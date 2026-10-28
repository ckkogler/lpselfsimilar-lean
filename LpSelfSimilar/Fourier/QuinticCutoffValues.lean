module

public import LpSelfSimilar.Fourier.QuinticCutoffSupport

@[expose] public section

/-!
# The actual cutoff takes values between zero and one

For widths at most one, one of the two clamped transition terms is one.
The remaining term lies in the unit interval. This proof covers the touching
bands at width one and does not introduce any extra positivity assumption.
-/

open Set
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- The even cutoff takes values in the closed unit interval for every admissible width. -/
theorem quinticFourierCutoff_mem_Icc {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (x : ℝ) :
    quinticFourierCutoff ε x ∈ Icc 0 1 := by
  by_cases hx : 0 ≤ x
  · have hc : quinticBandCoordinate ε (-x) ≤ 0 :=
      (quinticBandCoordinate_nonpos_iff hε).mpr (by linarith)
    rw [quinticFourierCutoff, clampedQuintic_of_nonpos hc, add_sub_cancel_right]
    exact clampedQuintic_mem_Icc _
  · have hc : quinticBandCoordinate ε x ≤ 0 :=
      (quinticBandCoordinate_nonpos_iff hε).mpr (by linarith)
    rw [quinticFourierCutoff, clampedQuintic_of_nonpos hc]
    have he (y : ℝ) : 1 + y - 1 = y := by ring
    rw [he]
    exact clampedQuintic_mem_Icc _

end LpSelfSimilar.Fourier
