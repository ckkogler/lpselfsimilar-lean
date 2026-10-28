module

public import LpSelfSimilar.Fourier.OscillatoryPhase
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section

/-!
# Angular-frequency integration by parts on a compact interval

Derivatives are required only in the interval's interior. Continuity and zero
endpoint values remove the boundary terms, so these lemmas apply to one smooth
piece of a globally piecewise cutoff. The twice-integrated identity includes
zero spatial frequency and never divides by it.
-/

open Set MeasureTheory

namespace LpSelfSimilar.Fourier

/-- One integration by parts, with zero endpoint values of the amplitude. -/
theorem integral_angularFourierPhase_mul_derivative {a b : ℝ} (hab : a ≤ b)
    {g g' : ℝ → ℂ} (hg : ContinuousOn g (Icc a b))
    (hd : ∀ ξ ∈ Ioo a b, HasDerivAt g (g' ξ) ξ)
    (hi : IntervalIntegrable g' volume a b) (ha : g a = 0) (hb : g b = 0) (x : ℝ) :
    (∫ ξ in a..b, angularFourierPhase x ξ * g' ξ) =
      -((x : ℂ) * Complex.I) * ∫ ξ in a..b, angularFourierPhase x ξ * g ξ := by
  have hp : Continuous (angularFourierPhase x) :=
    continuous_angularFourierPhase.comp (continuous_const.prodMk continuous_id)
  have hg₁ : ContinuousOn g (uIcc a b) := by rwa [uIcc_of_le hab]
  have hd₁ : ∀ ξ ∈ Ioo (min a b) (max a b), HasDerivAt g (g' ξ) ξ := by
    simpa only [min_eq_left hab, max_eq_right hab] using hd
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hp.continuousOn hg₁ (fun ξ hξ ↦ hasDerivAt_angularFourierPhase x ξ) hd₁
    ((continuous_const.mul hp).intervalIntegrable _ _) hi
  simp only [ha, hb, mul_zero, sub_self, zero_sub] at h
  simp_rw [mul_assoc] at h
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  simpa only [neg_mul, mul_assoc] using h

/-- Two integrations by parts when both amplitude and slope vanish at both endpoints. -/
theorem integral_angularFourierPhase_mul_secondDerivative {a b : ℝ} (hab : a ≤ b)
    {g g' g'' : ℝ → ℂ} (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ ξ ∈ Ioo a b, HasDerivAt g (g' ξ) ξ)
    (hd' : ∀ ξ ∈ Ioo a b, HasDerivAt g' (g'' ξ) ξ)
    (hi : IntervalIntegrable g'' volume a b)
    (ha : g a = 0) (hb : g b = 0) (ha' : g' a = 0) (hb' : g' b = 0) (x : ℝ) :
    (∫ ξ in a..b, angularFourierPhase x ξ * g'' ξ) =
      -(x : ℂ) ^ 2 * ∫ ξ in a..b, angularFourierPhase x ξ * g ξ := by
  have h1 := integral_angularFourierPhase_mul_derivative hab hg hd
    (hg'.intervalIntegrable_of_Icc hab) ha hb x
  have h2 := integral_angularFourierPhase_mul_derivative hab hg' hd' hi ha' hb' x
  rw [h2, h1]
  calc
    _ = ((x : ℂ) ^ 2 * Complex.I ^ 2) *
        ∫ ξ in a..b, angularFourierPhase x ξ * g ξ := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- The twice-integrated identity gives a quadratic spatial weight without division by frequency. -/
theorem one_add_sq_mul_integral_angularFourierPhase {a b : ℝ} (hab : a ≤ b)
    {g g' g'' : ℝ → ℂ} (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ ξ ∈ Ioo a b, HasDerivAt g (g' ξ) ξ)
    (hd' : ∀ ξ ∈ Ioo a b, HasDerivAt g' (g'' ξ) ξ)
    (hi : IntervalIntegrable g'' volume a b)
    (ha : g a = 0) (hb : g b = 0) (ha' : g' a = 0) (hb' : g' b = 0) (x : ℝ) :
    (1 + (x : ℂ) ^ 2) * (∫ ξ in a..b, angularFourierPhase x ξ * g ξ) =
      ∫ ξ in a..b, angularFourierPhase x ξ * (g ξ - g'' ξ) := by
  have hp : Continuous (angularFourierPhase x) :=
    continuous_angularFourierPhase.comp (continuous_const.prodMk continuous_id)
  have hgI : IntervalIntegrable (fun ξ ↦ angularFourierPhase x ξ * g ξ) volume a b :=
    (hp.continuousOn.mul hg).intervalIntegrable_of_Icc hab
  have hggI : IntervalIntegrable (fun ξ ↦ angularFourierPhase x ξ * g'' ξ) volume a b :=
    hi.continuousOn_mul hp.continuousOn
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hgI hggI,
    integral_angularFourierPhase_mul_secondDerivative hab hg hg' hd hd' hi ha hb ha' hb' x]
  ring

end LpSelfSimilar.Fourier
