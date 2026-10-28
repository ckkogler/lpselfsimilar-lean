module

public import LpSelfSimilar.Bernoulli.IntegratedDetailEnvelope
public import LpSelfSimilar.Bernoulli.PackingParameters
public import LpSelfSimilar.Analysis.IntegratedGaussianComparison

@[expose] public section

/-!
# The actual packing coefficient lies below its uniform envelope

The packing logarithm is inverted exactly, and the working criterion derives
the quadratic constraint in the inverse-square-root variable. The comparison
retains the full coefficient 2.4e18 and the correction 0.001/(t*chi).
-/

open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The packing logarithm recovers its entropy/separation ratio exactly. -/
theorem ratio_eq_exp_packingLogScale_div {J : ℝ} (hJ : 0 < J) :
    J = Real.exp (packingLogScale J) / 150 := by
  unfold packingLogScale
  rw [Real.exp_log (by positivity)]
  ring

/-- The working criterion gives the stated inverse-square-root bound on the logarithmic cost. -/
theorem packingLogScale_le_inverse_sqrt_gap {χ ρ L : ℝ}
    (hχ : 0 < χ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : χ * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2) :
    packingLogScale (L / ρ) ≤ (2 * χ) ^ (-(1 / 2 : ℝ)) := by
  have ht := six_lt_packingLogScale (three_le_separation_entropy_ratio hρ hρ1 hL)
  have hs : 0 < Real.sqrt (2 * χ) := Real.sqrt_pos.mpr (by positivity)
  have he : (packingLogScale (L / ρ) * Real.sqrt (2 * χ)) ^ 2 =
      2 * χ * (packingLogScale (L / ρ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hsq : (packingLogScale (L / ρ) * Real.sqrt (2 * χ)) ^ 2 ≤ 1 := by
    rw [he]
    nlinarith
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← one_div, le_div_iff₀ hs]
  nlinarith

/-- The normalized scale-integral coefficient is bounded by the exact envelope (5.7). -/
theorem integrated_coefficient_le_envelope {χ ρ L : ℝ}
    (hχ : 0 < χ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hsmall : χ * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2) :
    2400000000000000000 * (L / ρ) ^ 4 * packingLogScale (L / ρ) ^ 3 / χ ^ 2 *
      (1 + (1 / 1000 : ℝ) / (packingLogScale (L / ρ) * χ)) ^ 2 *
      Real.exp (-1 / (2 * χ)) ≤ integratedDetailEnvelope χ := by
  let t := packingLogScale (L / ρ)
  let u := (Real.sqrt χ)⁻¹
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have ht : 6 ≤ t := (six_lt_packingLogScale hJ).le
  have hu : 0 < u := inv_pos.mpr (Real.sqrt_pos.mpr hχ)
  have hu2 : u ^ 2 = χ⁻¹ := inv_sqrt_sq hχ
  have htu : 2 * t ^ 2 ≤ u ^ 2 := by
    rw [hu2, ← one_div, le_div_iff₀ hχ]
    change χ * t ^ 2 ≤ ρ / 2 at hsmall
    nlinarith
  have hj : L / ρ = Real.exp t / 150 := ratio_eq_exp_packingLogScale_div (by positivity)
  have hh := mul_le_mul_of_nonneg_left (integrated_coefficient_le_gaussian_profile ht hu.le htu)
    (by norm_num : (0 : ℝ) ≤ 2400000000000000000)
  have hex : Real.exp (-u ^ 2 / 2) = Real.exp (-1 / (2 * χ)) := by
    rw [hu2]
    congr 1
    ring
  have hu4 : u ^ 4 = (χ ^ 2)⁻¹ := by
    calc
      _ = (u ^ 2) ^ 2 := by ring
      _ = _ := by rw [hu2, inv_pow]
  have hcorr : 1 + u ^ 2 / (1000 * t) = 1 + (1 / 1000 : ℝ) / (t * χ) := by
    rw [hu2]
    field_simp
  change 2400000000000000000 * (L / ρ) ^ 4 * t ^ 3 / χ ^ 2 *
    (1 + (1 / 1000 : ℝ) / (t * χ)) ^ 2 * Real.exp (-1 / (2 * χ)) ≤
      integratedDetailEnvelope χ
  rw [hex, hu4, hcorr] at hh
  unfold integratedDetailEnvelope
  change _ ≤ 2400000000000000000 / ((150 : ℝ) ^ 4 * 2 * Real.sqrt 2) *
    polynomialGaussianEnvelope 6000 (2 * Real.sqrt 2) u
  rw [hj]
  convert! hh using 1 <;> ring

end LpSelfSimilar.Bernoulli
