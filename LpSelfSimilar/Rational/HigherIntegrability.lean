module

public import LpSelfSimilar.Rational.BoundedApproximation
public import LpSelfSimilar.Bernoulli.QuantitativeGain
public import LpSelfSimilar.Bernoulli.IntegrabilityExponent
public import LpSelfSimilar.Analysis.SupportedDensity

@[expose] public section

/-!
Full rational Proposition 3.1, with exactly the exponent in equation (3.1).
The rational detail argument proves bounded approximation; the preserved
Theorem 1.1 and exact Lemma 2.1 give the gain. The derived compact interval
allows the final decrease from the exact lemma exponent to the paper's exponent.
-/

open MeasureTheory Set Real
open LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Rational

/-- One absolute threshold for the quantitative rational Lp theorem. -/
noncomputable def higherIntegrabilityThreshold : ℝ := approximationThreshold (1 / (2 * 21 ^ 2))

lemma higherIntegrabilityThreshold_pos : 0 < higherIntegrabilityThreshold :=
  approximationThreshold_pos (by norm_num)

/-- Rational Proposition 3.1, with a supported nonnegative density and the
explicit equality to its weighted Lebesgue measure. No analytic input is assumed. -/
theorem higher_integrability {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a.Coprime b)
    (hl0 : 1 / 2 ≤ (a : ℝ) / b) (hl1 : (a : ℝ) / b < 1)
    (hsmall : -log ((a : ℝ) / b) * complexity b ^ 10 ≤ higherIntegrabilityThreshold) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      convolution ((a : ℝ) / b) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      MemLp f (ENNReal.ofReal (1 + integrabilityGain ((a : ℝ) / b))) volume ∧
      (∀ x, x ∉ Icc (-(1 - (a : ℝ) / b)⁻¹) (1 - (a : ℝ) / b)⁻¹ → f x = 0) := by
  obtain ⟨f, f₀, hf0, hf, hrep, _, hf₀, hbound, herr⟩ :=
    bounded_density_approximation (by norm_num : (0 : ℝ) < 1 / (2 * 21 ^ 2))
      ha hb hab hl0 hl1 hsmall
  obtain ⟨g, hg0, hg, hgrep, hLp⟩ := higher_integrability_of_bounded_approximation hl0 hl1
    hf hf0 hrep hf₀ (fun x ↦ (hbound x).2) herr
  exact exists_supported_density_memLp hg hg0 hgrep measurableSet_Icc
    (convolution_compl_interval _ (by linarith) hl1)
    (by simp [Real.volume_Icc]) hLp
    (ENNReal.ofReal_le_ofReal (integrabilityGain_le_exact hl0 hl1))

end LpSelfSimilar.Rational
