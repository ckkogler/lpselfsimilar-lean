module

public import LpSelfSimilar.Fourier.QuinticCutoffSupport
public import LpSelfSimilar.Analysis.QuinticDetailProfile

@[expose] public section

/-!
# One transition band of the Fourier detail multiplier

The even detail splits into a positive-band function and its reflection. The
positive-band function and its derivative vanish at both endpoints, so their
integrals reduce exactly to the closed transition interval without boundary terms.
-/

open Set MeasureTheory
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Fourier

/-- The positive-band contribution, extended by zero by the clamped slope. -/
noncomputable def quinticDetailBand (ε x : ℝ) : ℝ :=
  -x * clampedQuinticSlope (quinticBandCoordinate ε x) / (2 * ε)

/-- Its everywhere-defined first derivative. -/
noncomputable def quinticDetailBandSlope (ε x : ℝ) : ℝ :=
  -clampedQuinticSlope (quinticBandCoordinate ε x) / (2 * ε) -
    x * clampedQuinticCurvature (quinticBandCoordinate ε x) / (2 * ε) ^ 2

/-- Derivative of the positive-band detail, including both joins. -/
theorem hasDerivAt_quinticDetailBand {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    HasDerivAt (quinticDetailBand ε) (quinticDetailBandSlope ε x) x := by
  have hs := (hasDerivAt_clampedQuinticSlope (quinticBandCoordinate ε x)).comp x
    (hasDerivAt_quinticBandCoordinate ε x)
  convert! ((hasDerivAt_id x).neg.mul hs).div_const (2 * ε) using 1 <;>
    simp only [quinticDetailBand, quinticDetailBandSlope, Pi.neg_apply, Function.comp_apply, id_eq]
  field_simp
  <;> ring

/-- The full detail is the sum of the two reflected band contributions. -/
theorem quinticFourierDetail_eq_bands (ε x : ℝ) :
    quinticFourierDetail ε x = quinticDetailBand ε x + quinticDetailBand ε (-x) := by
  unfold quinticFourierDetail
  rw [(hasDerivAt_quinticFourierCutoff ε x).deriv]
  unfold quinticFourierCutoffSlope quinticDetailBand
  ring

/-- The full detail slope is the difference of the reflected band slopes. -/
theorem quinticFourierDetailSlope_eq_bands (ε x : ℝ) :
    quinticFourierDetailSlope ε x =
      quinticDetailBandSlope ε x - quinticDetailBandSlope ε (-x) := by
  unfold quinticFourierDetailSlope quinticFourierCutoffSlope
    quinticFourierCutoffCurvature quinticDetailBandSlope
  ring

/-- The band function and its slope vanish outside the open positive band. -/
theorem quinticDetailBand_eq_zero {ε x : ℝ} (hε : 0 < ε)
    (hx : x ≤ 1 - ε ∨ 1 + ε ≤ x) :
    quinticDetailBand ε x = 0 ∧ quinticDetailBandSlope ε x = 0 := by
  have hu : quinticBandCoordinate ε x ≤ 0 ∨ 1 ≤ quinticBandCoordinate ε x := by
    rcases hx with h | h
    · exact Or.inl ((quinticBandCoordinate_nonpos_iff hε).mpr h)
    · exact Or.inr ((one_le_quinticBandCoordinate_iff hε).mpr h)
  simp [quinticDetailBand, quinticDetailBandSlope,
    clampedQuinticSlope_eq_zero hu, clampedQuinticCurvature_eq_zero hu]

/-- The band function has its exact rescaled profile on the entire closed band. -/
theorem quinticDetailBand_eq_profile {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Icc (1 - ε) (1 + ε)) :
    quinticDetailBand ε x = quinticDetailProfile ε (quinticBandCoordinate ε x) / (2 * ε) := by
  have hu := (quinticBandCoordinate_mem_Icc_iff hε).mpr hx
  unfold quinticDetailBand quinticDetailProfile
  rw [clampedQuinticSlope_eq_of_mem_Icc hu]
  unfold quinticBandCoordinate
  field_simp
  <;> ring

/-- The band slope has its exact rescaled profile derivative on the closed band. -/
theorem quinticDetailBandSlope_eq_profile {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Icc (1 - ε) (1 + ε)) :
    quinticDetailBandSlope ε x =
      quinticDetailProfileSlope ε (quinticBandCoordinate ε x) / (2 * ε) ^ 2 := by
  have hu := (quinticBandCoordinate_mem_Icc_iff hε).mpr hx
  unfold quinticDetailBandSlope quinticDetailProfileSlope
  rw [clampedQuinticSlope_eq_of_mem_Icc hu, clampedQuinticCurvature_eq_of_mem_Icc hu]
  unfold quinticBandCoordinate
  field_simp
  <;> ring

/-- The band multiplier has compact support. -/
theorem hasCompactSupport_quinticDetailBand {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (quinticDetailBand ε) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (1 - ε) (1 + ε)))
  intro x hx
  apply (quinticDetailBand_eq_zero hε _).1
  by_cases h : x ≤ 1 - ε
  · exact Or.inl h
  · exact Or.inr (le_of_not_ge (fun h' ↦ hx ⟨(lt_of_not_ge h).le, h'⟩))

/-- The band multiplier's slope has compact support. -/
theorem hasCompactSupport_quinticDetailBandSlope {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (quinticDetailBandSlope ε) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (1 - ε) (1 + ε)))
  intro x hx
  apply (quinticDetailBand_eq_zero hε _).2
  by_cases h : x ≤ 1 - ε
  · exact Or.inl h
  · exact Or.inr (le_of_not_ge (fun h' ↦ hx ⟨(lt_of_not_ge h).le, h'⟩))

end LpSelfSimilar.Fourier
