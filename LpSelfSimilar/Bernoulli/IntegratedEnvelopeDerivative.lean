module

public import LpSelfSimilar.Bernoulli.IntegratedDetailEnvelope
public import LpSelfSimilar.Analysis.InverseSquareRootDerivative
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# The actual logarithmic derivative of the detail envelope

The inverse-square-root chain rule proves the logarithmic derivative stated in
the smallness argument. Its explicit lower bound is positive throughout the
whole allowed gap interval, independently checking the monotonicity estimate.
-/

open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- Exact derivative of log(envelope) with respect to log(gap). -/
noncomputable def integratedDetailEnvelopeLogSlope (χ : ℝ) : ℝ :=
  -(7 / 2 : ℝ) - 2 / (1 + 6000 * χ) + 1 / (2 * χ) - Real.sqrt 2 / Real.sqrt χ

/-- The ordinary derivative of the logarithm of the actual envelope. -/
theorem hasDerivAt_log_integratedDetailEnvelope {χ : ℝ} (hχ : 0 < χ) :
    HasDerivAt (fun x => Real.log (integratedDetailEnvelope x))
      (integratedDetailEnvelopeLogSlope χ / χ) χ := by
  let u := (Real.sqrt χ)⁻¹
  let C := 2400000000000000000 / ((150 : ℝ) ^ 4 * 2 * Real.sqrt 2)
  let G := polynomialGaussianEnvelope 6000 (2 * Real.sqrt 2) u
  let P := 7 / u + 4 * u / (6000 + u ^ 2) - u + 2 * Real.sqrt 2
  have hu : 0 < u := inv_pos.mpr (Real.sqrt_pos.mpr hχ)
  have hC : 0 < C := by dsimp [C]; positivity
  have hG : 0 < G := polynomialGaussianEnvelope_pos (by norm_num) hu _
  have hu2 : u ^ 2 = χ⁻¹ := inv_sqrt_sq hχ
  have hden : 6000 + u ^ 2 ≠ 0 := by positivity
  have hdenχ : 1 + 6000 * χ ≠ 0 := by positivity
  have hPS : P * (-u / 2) = integratedDetailEnvelopeLogSlope χ := by
    calc
      _ = -(7 / 2 : ℝ) - 2 * u ^ 2 / (6000 + u ^ 2) + u ^ 2 / 2 - Real.sqrt 2 * u := by
        dsimp only [P]
        field_simp
        ring
      _ = _ := by
        rw [hu2]
        unfold integratedDetailEnvelopeLogSlope
        change -(7 / 2 : ℝ) - 2 * χ⁻¹ / (6000 + χ⁻¹) + χ⁻¹ / 2 - Real.sqrt 2 * u =
          -(7 / 2 : ℝ) - 2 / (1 + 6000 * χ) + 1 / (2 * χ) - Real.sqrt 2 * u
        field_simp
        ring
  have h := ((hasDerivAt_polynomialGaussianEnvelope (by norm_num : (0 : ℝ) < 6000)
    hu (2 * Real.sqrt 2)).comp χ (hasDerivAt_inv_sqrt hχ)).const_mul C
  change HasDerivAt integratedDetailEnvelope (C * (G * P * (-u / (2 * χ)))) χ at h
  have hl := h.log (integratedDetailEnvelope_pos hχ).ne'
  apply hl.congr_deriv
  change C * (G * P * (-u / (2 * χ))) / (C * G) = integratedDetailEnvelopeLogSlope χ / χ
  calc
    _ = P * (-u / 2) / χ := by
      field_simp [hC.ne', hG.ne', hχ.ne']
    _ = _ := by rw [hPS]

/-- Exact derivative with respect to the logarithm of the gap, as used in (5.7). -/
theorem hasDerivAt_logarithmic_integratedDetailEnvelope {χ : ℝ} (hχ : 0 < χ) :
    HasDerivAt (fun v => Real.log (integratedDetailEnvelope (Real.exp v)))
      (integratedDetailEnvelopeLogSlope χ) (Real.log χ) := by
  have ho : HasDerivAt (fun x => Real.log (integratedDetailEnvelope x))
      (integratedDetailEnvelopeLogSlope χ / χ) (Real.exp (Real.log χ)) := by
    rw [Real.exp_log hχ]
    exact hasDerivAt_log_integratedDetailEnvelope hχ
  convert! ho.comp (Real.log χ) (Real.hasDerivAt_exp (Real.log χ)) using 1 <;>
    simp [Real.exp_log hχ, hχ.ne']

/-- The actual logarithmic slope has exactly the lower bound stated in the argument. -/
theorem integratedDetailEnvelopeLogSlope_lower_bound {χ : ℝ} (hχ : 0 < χ) :
    1 / (2 * χ) - 2 / Real.sqrt χ - 11 / 2 ≤ integratedDetailEnvelopeLogSlope χ := by
  have hf : 2 / (1 + 6000 * χ) ≤ (2 : ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hs : Real.sqrt 2 / Real.sqrt χ ≤ 2 / Real.sqrt χ :=
    div_le_div_of_nonneg_right (by linarith [gaussianEnvelope_sqrt_two_bounds.2])
      (Real.sqrt_nonneg _)
  unfold integratedDetailEnvelopeLogSlope
  linarith

/-- The stated lower bound is strictly positive on the entire allowed interval. -/
theorem integratedDetailEnvelope_logSlope_lower_pos {χ : ℝ}
    (hχ : 0 < χ) (hχ250 : χ ≤ 1 / 250) :
    0 < 1 / (2 * χ) - 2 / Real.sqrt χ - 11 / 2 := by
  let u := (Real.sqrt χ)⁻¹
  have hu : 15 ≤ u := gaussianEnvelope_sqrt_two_hundred_fifty_bounds.1.le.trans
    (sqrt_two_hundred_fifty_le_inv_sqrt hχ hχ250)
  have he : 1 / (2 * χ) = u ^ 2 / 2 := by rw [inv_sqrt_sq hχ]; ring
  rw [he]
  change 0 < u ^ 2 / 2 - 2 * u - 11 / 2
  nlinarith [mul_nonneg (sub_nonneg.mpr hu) (show 0 ≤ u + 11 by linarith)]

end LpSelfSimilar.Bernoulli
