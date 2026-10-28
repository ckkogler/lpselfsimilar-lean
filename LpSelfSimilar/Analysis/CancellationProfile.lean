module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
# The concave scalar cancellation profile

The finite entropy estimate also has a short calculus proof. This module
records its displayed profile and exact second derivative. The earlier
polynomial proof of the same cancellation bound remains unchanged.
For 0 <= gamma < 2 the radicand is positive on the whole real line, so every
ordinary derivative used here is justified, including at the chord endpoints.
-/

open Real Set

namespace LpSelfSimilar.Analysis

noncomputable def cancellationProfile (γ x : ℝ) : ℝ :=
  1 - sqrt (1 - 2 * γ * x * (1 - x))

noncomputable def cancellationProfileSlope (γ x : ℝ) : ℝ :=
  γ * (1 - 2 * x) / sqrt (1 - 2 * γ * x * (1 - x))

/-- Completing the square keeps the radicand strictly positive everywhere. -/
theorem cancellationProfile_radicand_pos {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ < 2)
    (x : ℝ) : 0 < 1 - 2 * γ * x * (1 - x) := by
  have h := mul_nonneg hγ (sq_nonneg (x - 1 / 2))
  nlinarith

/-- The profile's exact first derivative. -/
theorem hasDerivAt_cancellationProfile {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ < 2) (x : ℝ) :
    HasDerivAt (cancellationProfile γ) (cancellationProfileSlope γ x) x := by
  have hq : HasDerivAt (fun y : ℝ => 1 - 2 * γ * y * (1 - y))
      (-2 * γ * (1 - 2 * x)) x := by
    convert! (hasDerivAt_const x 1).sub (((hasDerivAt_id x).const_mul (2 * γ)).mul
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x))) using 1 <;> simp only [Pi.sub_apply, id_eq] <;> ring
  have hp := cancellationProfile_radicand_pos hγ hγ2 x
  have hs := (sqrt_pos.mpr hp).ne'
  convert! (hasDerivAt_const x 1).sub (hq.sqrt hp.ne') using 1 <;>
    dsimp [cancellationProfile, cancellationProfileSlope] <;> field_simp <;> ring

/-- The exact curvature, with the denominator written as the cube of the positive square root. -/
theorem hasDerivAt_cancellationProfileSlope {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ < 2) (x : ℝ) :
    HasDerivAt (cancellationProfileSlope γ)
      (γ * (γ - 2) / (sqrt (1 - 2 * γ * x * (1 - x))) ^ 3) x := by
  have hp := cancellationProfile_radicand_pos hγ hγ2 x
  have hs : sqrt (1 - 2 * γ * x * (1 - x)) ≠ 0 := (sqrt_pos.mpr hp).ne'
  have hq : HasDerivAt (fun y : ℝ => 1 - 2 * γ * y * (1 - y))
      (-2 * γ * (1 - 2 * x)) x := by
    convert! (hasDerivAt_const x 1).sub (((hasDerivAt_id x).const_mul (2 * γ)).mul
      ((hasDerivAt_const x 1).sub (hasDerivAt_id x))) using 1 <;> simp only [Pi.sub_apply, id_eq] <;> ring
  have hn : HasDerivAt (fun y : ℝ => γ * (1 - 2 * y)) (-2 * γ) x := by
    convert! ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).const_mul 2)).const_mul γ using 1 <;> ring
  convert! hn.div (hq.sqrt hp.ne') hs using 1
  field_simp
  congr 1
  rw [Real.sq_sqrt (by nlinarith : 0 ≤ 1 - γ * 2 * x * (1 - x))]
  ring

/-- The actual second derivative equals the displayed curvature. -/
theorem deriv_deriv_cancellationProfile {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ < 2) (x : ℝ) :
    deriv (deriv (cancellationProfile γ)) x =
      γ * (γ - 2) / (sqrt (1 - 2 * γ * x * (1 - x))) ^ 3 := by
  rw [show deriv (cancellationProfile γ) = cancellationProfileSlope γ from
    funext (fun y => (hasDerivAt_cancellationProfile hγ hγ2 y).deriv)]
  exact (hasDerivAt_cancellationProfileSlope hγ hγ2 x).deriv

/-- The same curvature in the source's exact real exponent 3/2 notation. -/
theorem deriv_deriv_cancellationProfile_rpow {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ < 2) (x : ℝ) :
    deriv (deriv (cancellationProfile γ)) x =
      γ * (γ - 2) / (1 - 2 * γ * x * (1 - x)) ^ ((3 : ℝ) / 2) := by
  have hp := cancellationProfile_radicand_pos hγ hγ2 x
  have he : (1 - 2 * γ * x * (1 - x)) ^ ((3 : ℝ) / 2) =
      (sqrt (1 - 2 * γ * x * (1 - x))) ^ 3 := by
    rw [Real.rpow_div_two_eq_sqrt _ hp.le]
    norm_num
  rw [he]
  exact deriv_deriv_cancellationProfile hγ hγ2 x

/-- The displayed second derivative is strictly negative for 0<gamma<2. -/
theorem deriv_deriv_cancellationProfile_neg {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (x : ℝ) :
    deriv (deriv (cancellationProfile γ)) x < 0 := by
  rw [deriv_deriv_cancellationProfile hγ.le hγ2]
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hγ (by linarith))
    (pow_pos (sqrt_pos.mpr (cancellationProfile_radicand_pos hγ.le hγ2 x)) 3)

/-- Concavity on the whole real line, hence also on the required half-unit interval. -/
theorem concaveOn_cancellationProfile {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ < 2) :
    ConcaveOn ℝ univ (cancellationProfile γ) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
    (fun x _ => (hasDerivAt_cancellationProfile hγ hγ2 x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_cancellationProfile hγ hγ2 x).hasDerivWithinAt)
    (fun x _ => (hasDerivAt_cancellationProfileSlope hγ hγ2 x).hasDerivWithinAt)
  intro x hx
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hγ (by linarith))
    (by positivity)

/-- The exact chord bound for gamma=3/5. -/
theorem cancellationProfile_three_fifths_chord {x : ℝ} (hx : x ∈ Icc 0 (1 / 2)) :
    2 * (1 - sqrt (7 / 10)) * x ≤ cancellationProfile (3 / 5) x := by
  have h := (concaveOn_cancellationProfile (by norm_num : (0 : ℝ) ≤ 3 / 5)
    (by norm_num : (3 / 5 : ℝ) < 2)).2
    (mem_univ (0 : ℝ)) (mem_univ (1 / 2 : ℝ))
    (show 0 ≤ 1 - 2 * x by linarith [hx.2]) (show 0 ≤ 2 * x by linarith [hx.1]) (by ring)
  have he : (1 - 2 * x) * 0 + 2 * x * (1 / 2) = x := by ring
  simp only [smul_eq_mul, he] at h
  have hz : cancellationProfile (3 / 5) 0 = 0 := by norm_num [cancellationProfile]
  have hh : cancellationProfile (3 / 5) (1 / 2) = 1 - sqrt (7 / 10) := by
    norm_num [cancellationProfile]
  rw [hz, hh, mul_zero, zero_add] at h
  nlinarith

/-- The chord coefficient is strictly greater than the required 13/40. -/
theorem cancellationProfile_chord_coefficient_gt :
    (13 / 40 : ℝ) < 2 * (1 - sqrt (7 / 10)) := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 10)
  have hs := Real.sqrt_nonneg (7 / 10 : ℝ)
  nlinarith

end LpSelfSimilar.Analysis
