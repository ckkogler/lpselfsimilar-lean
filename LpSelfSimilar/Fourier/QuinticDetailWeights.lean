module

public import LpSelfSimilar.Fourier.QuinticDetailCurvatureIntegrals

@[expose] public section

/-!
# Support and integral bounds for the three detail weights

The explicit slope and almost-everywhere curvature are the weights in the
product rule. They vanish off the same two frequency bands as the detail, so
mean amplitude bounds are needed only on those bands.
-/

open MeasureTheory

namespace LpSelfSimilar.Fourier

/-- All three detail formulas vanish outside the symmetric closed frequency band. -/
theorem quinticDetail_formulas_zero_off_band {ε x : ℝ} (hε : 0 < ε)
    (hx : ε < |(|x| - 1)|) :
    quinticFourierDetail ε x = 0 ∧ quinticFourierDetailSlope ε x = 0 ∧
      quinticFourierDetailCurvature ε x = 0 := by
  have ho (y : ℝ) (hy : |y| = |x|) : y ≤ 1 - ε ∨ 1 + ε ≤ y := by
    by_cases h : y ≤ 1 - ε
    · exact Or.inl h
    · right
      by_contra h'
      have hl : 1 - ε < y := lt_of_not_ge h
      have hr : y < 1 + ε := lt_of_not_ge h'
      have ha : |y| ≤ 1 + ε := abs_le.mpr ⟨by linarith, hr.le⟩
      have hb : 1 - ε ≤ |y| := hl.le.trans (le_abs_self y)
      have hh : |(|y| - 1)| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
      rw [hy] at hh
      exact (not_le_of_gt hx) hh
  have hp := ho x rfl
  have hn := ho (-x) (abs_neg x)
  have hpq := quinticDetailBand_eq_zero hε hp
  have hnq := quinticDetailBand_eq_zero hε hn
  rw [quinticFourierDetail_eq_bands, quinticFourierDetailSlope_eq_bands]
  simp [quinticFourierDetailCurvature, hpq.1, hpq.2, hnq.1, hnq.2,
    quinticDetailBandCurvature_eq_zero hp, quinticDetailBandCurvature_eq_zero hn]

/-- The explicit detail slope is integrable because it is the actual first derivative. -/
theorem integrable_quinticFourierDetailSlope {ε : ℝ} (hε : 0 < ε) :
    Integrable (quinticFourierDetailSlope ε) := by
  have he : deriv (quinticFourierDetail ε) = quinticFourierDetailSlope ε :=
    funext (fun x ↦ (hasDerivAt_quinticFourierDetail (ne_of_gt hε) x).deriv)
  rw [← he]
  exact integrable_deriv_quinticFourierDetail hε

/-- The three explicit product-rule weights have the exact proved integral bounds. -/
theorem quinticDetail_formula_integral_bounds {ε : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1 / 100000) :
    (∫ x, |quinticFourierDetail ε x|) ≤ 21 / 10 ∧
      (∫ x, |quinticFourierDetailSlope ε x|) ≤ 7 / ε ∧
        (∫ x, |quinticFourierDetailCurvature ε x|) ≤ 32 / ε ^ 2 := by
  have h := quinticFourierDetail_integral_bounds hε hεsmall
  have he : deriv (quinticFourierDetail ε) = quinticFourierDetailSlope ε :=
    funext (fun x ↦ (hasDerivAt_quinticFourierDetail (ne_of_gt hε) x).deriv)
  have he₂ : (∫ x, |quinticFourierDetailCurvature ε x|) =
      ∫ x, |deriv (deriv (quinticFourierDetail ε)) x| := by
    apply integral_congr_ae
    filter_upwards [ae_deriv_deriv_quinticFourierDetail hε] with x hx
    rw [hx]
  exact ⟨h.1, by simpa only [he] using h.2.1, by rw [he₂]; exact h.2.2⟩

end LpSelfSimilar.Fourier
