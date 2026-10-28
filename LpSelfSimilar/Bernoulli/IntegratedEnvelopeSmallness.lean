module

public import LpSelfSimilar.Bernoulli.IntegratedDetailEnvelope
public import LpSelfSimilar.Analysis.GaussianEnvelopeEndpoint

@[expose] public section

/-!
# The uniform smallness bound for the integrated-detail envelope

The exact endpoint certificate and proved monotonicity give a uniform bound
throughout the full allowed gap interval, including its non-strict upper endpoint.
-/

open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- The endpoint has the strict seven-times-ten-to-the-minus-eighteen margin. -/
theorem integratedDetailEnvelope_endpoint_lt :
    integratedDetailEnvelope (1 / 250 : ℝ) < (7 : ℝ) / 10 ^ 18 := by
  have hu : (Real.sqrt (1 / 250 : ℝ))⁻¹ = Real.sqrt 250 := by
    rw [← Real.sqrt_inv]
    norm_num
  unfold integratedDetailEnvelope
  rw [hu]
  exact gaussianEnvelope_endpoint_lt

/-- The endpoint margin holds uniformly over all admissible positive gaps. -/
theorem integratedDetailEnvelope_uniform_endpoint_bound {χ : ℝ}
    (hχ : 0 < χ) (hχ250 : χ ≤ 1 / 250) :
    integratedDetailEnvelope χ < (7 : ℝ) / 10 ^ 18 :=
  (strictMonoOn_integratedDetailEnvelope.monotoneOn ⟨hχ, hχ250⟩
    (by norm_num : (1 / 250 : ℝ) ∈ Set.Ioc 0 (1 / 250)) hχ250).trans_lt
      integratedDetailEnvelope_endpoint_lt

/-- The exact uniform one-hundredth bound required for removing smoothing. -/
theorem integratedDetailEnvelope_lt_one_hundredth {χ : ℝ}
    (hχ : 0 < χ) (hχ250 : χ ≤ 1 / 250) : integratedDetailEnvelope χ < (1 / 100 : ℝ) :=
  (integratedDetailEnvelope_uniform_endpoint_bound hχ hχ250).trans (by norm_num)

end LpSelfSimilar.Bernoulli
