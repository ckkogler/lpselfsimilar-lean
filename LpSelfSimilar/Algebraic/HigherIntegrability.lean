module

public import LpSelfSimilar.Algebraic.BoundedApproximation
public import LpSelfSimilar.Bernoulli.QuantitativeGain
public import LpSelfSimilar.Bernoulli.IntegrabilityExponent
public import LpSelfSimilar.Analysis.SupportedDensity

@[expose] public section

/-!
Full revised algebraic Proposition 3.1, with exactly the exponent in equation (3.1).
The algebraic detail argument proves bounded approximation; the preserved
Theorem 1.1 and exact Lemma 2.1 give the gain. The derived compact interval
allows the final decrease from the exact lemma exponent to the paper's exponent.
-/

open MeasureTheory Set Real
open LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Algebraic

/-- Revised algebraic Proposition 3.1, with a supported nonnegative density and the
explicit equality to its weighted Lebesgue measure. No analytic input is assumed. -/
theorem higher_integrability {l : ℝ} (hlalg : IsAlgebraic ℚ l)
    (hl0 : 1 / 2 < l) (hl1 : l < 1)
    (hsmall : -log l * complexity l ^ 10 ≤ 1 / (10 : ℝ) ^ 100) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      MemLp f (ENNReal.ofReal (1 + integrabilityGain l)) volume ∧
      (∀ x, x ∉ Icc (-(1 - l)⁻¹) (1 - l)⁻¹ → f x = 0) := by
  obtain ⟨f, f₀, hf0, hf, hrep, _, hf₀, hbound, herr⟩ :=
    bounded_density_approximation hlalg hl0 hl1 hsmall
  obtain ⟨g, hg0, hg, hgrep, hLp⟩ := higher_integrability_of_bounded_approximation hl0.le hl1
    hf hf0 hrep hf₀ (fun x ↦ (hbound x).2) herr
  exact exists_supported_density_memLp hg hg0 hgrep measurableSet_Icc
    (convolution_compl_interval _ (by linarith) hl1)
    (by simp [Real.volume_Icc]) hLp
    (ENNReal.ofReal_le_ofReal (integrabilityGain_le_exact hl0.le hl1))

end LpSelfSimilar.Algebraic
