module

public import LpSelfSimilar.Fourier.QuinticCutoffSupport
public import LpSelfSimilar.Analysis.ZeroExtendedDerivative

@[expose] public section

/-!
# One transition band of the cutoff slope

The slope band and its first derivative vanish at both endpoints. Its second
derivative is a zero-extended polynomial, with jumps allowed at the endpoints.
Only the interior derivative identity is needed for the integration-by-parts
argument; the global slope band remains C1.
-/

open Set MeasureTheory Filter
open LpSelfSimilar.Analysis
open scoped Topology

namespace LpSelfSimilar.Fourier

/-- The positive transition contribution to the actual cutoff slope. -/
noncomputable def quinticSlopeBand (ε x : ℝ) : ℝ :=
  clampedQuinticSlope (quinticBandCoordinate ε x) / (2 * ε)

/-- The actual first derivative of the positive slope band. -/
noncomputable def quinticSlopeBandDerivative (ε x : ℝ) : ℝ :=
  clampedQuinticCurvature (quinticBandCoordinate ε x) / (2 * ε) ^ 2

/-- The second derivative off the two exceptional endpoints, with zero endpoint values. -/
noncomputable def quinticSlopeBandSecond (ε : ℝ) : ℝ → ℝ :=
  (Ioo (1 - ε) (1 + ε)).indicator
    (fun x => quinticTransitionThird (quinticBandCoordinate ε x) / (2 * ε) ^ 3)

/-- The full cutoff slope is the positive band minus its reflection. -/
theorem quinticFourierCutoffSlope_eq_slopeBands (ε x : ℝ) :
    quinticFourierCutoffSlope ε x = quinticSlopeBand ε x - quinticSlopeBand ε (-x) := by
  unfold quinticFourierCutoffSlope quinticSlopeBand
  ring

/-- The band derivative formula holds everywhere, including both joins. -/
theorem hasDerivAt_quinticSlopeBand {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    HasDerivAt (quinticSlopeBand ε) (quinticSlopeBandDerivative ε x) x := by
  convert! ((hasDerivAt_clampedQuinticSlope (quinticBandCoordinate ε x)).comp x
    (hasDerivAt_quinticBandCoordinate ε x)).div_const (2 * ε) using 1 <;>
    simp only [quinticSlopeBand, quinticSlopeBandDerivative, Function.comp_def] <;>
    field_simp <;> ring

/-- Both the slope band and its first derivative vanish outside its open transition interval. -/
theorem quinticSlopeBand_zero_off {ε x : ℝ} (hε : 0 < ε)
    (hx : x ≤ 1 - ε ∨ 1 + ε ≤ x) :
    quinticSlopeBand ε x = 0 ∧ quinticSlopeBandDerivative ε x = 0 := by
  have hc : quinticBandCoordinate ε x ≤ 0 ∨ 1 ≤ quinticBandCoordinate ε x := by
    rcases hx with hx | hx
    · exact Or.inl ((quinticBandCoordinate_nonpos_iff hε).mpr hx)
    · exact Or.inr ((one_le_quinticBandCoordinate_iff hε).mpr hx)
  simp only [quinticSlopeBand, quinticSlopeBandDerivative,
    clampedQuinticSlope_eq_zero hc, clampedQuinticCurvature_eq_zero hc, zero_div, and_self]

/-- The actual band derivative is continuous because the clamped curvature is continuous. -/
theorem continuous_quinticSlopeBandDerivative (ε : ℝ) :
    Continuous (quinticSlopeBandDerivative ε) := by
  unfold quinticSlopeBandDerivative
  exact (continuous_clampedQuinticCurvature.comp (by unfold quinticBandCoordinate; fun_prop)).div_const _

/-- The zero-extended second derivative vanishes at and beyond either endpoint. -/
theorem quinticSlopeBandSecond_zero_off {ε x : ℝ}
    (hx : x ≤ 1 - ε ∨ 1 + ε ≤ x) : quinticSlopeBandSecond ε x = 0 := by
  apply indicator_of_notMem
  intro h
  rcases hx with hx | hx
  · exact (not_lt_of_ge hx) h.1
  · exact (not_lt_of_ge hx) h.2

/-- The second derivative formula is the actual derivative throughout the open band. -/
theorem hasDerivAt_quinticSlopeBandDerivative_of_mem {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Ioo (1 - ε) (1 + ε)) :
    HasDerivAt (quinticSlopeBandDerivative ε) (quinticSlopeBandSecond ε x) x := by
  rw [quinticSlopeBandSecond, indicator_of_mem hx]
  have hd : HasDerivAt (fun y => quinticTransitionCurvature (quinticBandCoordinate ε y) / (2 * ε) ^ 2)
      (quinticTransitionThird (quinticBandCoordinate ε x) / (2 * ε) ^ 3) x := by
    convert! ((hasDerivAt_quinticTransitionCurvature (quinticBandCoordinate ε x)).comp x
      (hasDerivAt_quinticBandCoordinate ε x)).div_const ((2 * ε) ^ 2) using 1 <;>
      field_simp <;> ring
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  unfold quinticSlopeBandDerivative
  rw [clampedQuinticCurvature_eq_of_mem_Icc
    ((quinticBandCoordinate_mem_Icc_iff hε).mpr ⟨hy.1.le, hy.2.le⟩)]

/-- The zero-extended polynomial second derivative is integrable. -/
theorem integrable_quinticSlopeBandSecond (ε : ℝ) :
    Integrable (quinticSlopeBandSecond ε) := by
  have hc : Continuous (fun x => quinticTransitionThird (quinticBandCoordinate ε x) / (2 * ε) ^ 3) := by
    unfold quinticTransitionThird quinticBandCoordinate
    fun_prop
  exact (integrable_indicator_iff measurableSet_Ioo).mpr
    ((hc.integrableOn_Icc (μ := volume)).mono_set Ioo_subset_Icc_self)

end LpSelfSimilar.Fourier
