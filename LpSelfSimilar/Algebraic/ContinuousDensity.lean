module

public import LpSelfSimilar.Algebraic.PowerIntegrability
public import LpSelfSimilar.Bernoulli.ContinuousDensity

@[expose] public section

/-!
The full algebraic Theorem 1.2 of On Lp density of self similar measures and Bernoulli convolutions. The measure is the actual law of
independent fair-sign series; degree and Mahler measure are canonical. The proof
selects a powered parameter, proves its precise Lp density, splits digits into
residue classes and applies the already proved Young/translation argument.
Compact support and pointwise nonnegativity are conclusions.
-/

open MeasureTheory Real

namespace LpSelfSimilar

/-- The stronger complexity criterion established in the proof of Theorem 1.2. -/
theorem algebraic_bernoulli_continuous_density_of_gap {l : ℝ}
    (hlalg : IsAlgebraic ℚ l) (hl0 : 1 / 2 < l) (hl1 : l < 1)
    (hsmall : (1 - l) * Algebraic.complexity l ^ 100 < 2) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Continuous f ∧ HasCompactSupport f ∧
      Bernoulli.convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  obtain ⟨k, hk, f, hfn, hf, hrep, hLp, _hsupp⟩ :=
    Algebraic.exists_power_density hlalg hl0.le hl1 hsmall
  exact Bernoulli.continuous_density_of_power_memLp (by linarith) hl1 hk hf hfn hrep hLp

/-- **Theorem 1.2 of On Lp density of self similar measures and Bernoulli convolutions**, with its exact canonical degree/Mahler expression
and exponent 100. No analytic or geometric assumption is added. -/
theorem algebraic_bernoulli_convolution_continuous_density {l : ℝ}
    (hlalg : IsAlgebraic ℚ l) (hl0 : 1 / 2 < l) (hl1 : l < 1)
    (hsmall : 1 - (min 1 (Real.log (Algebraic.mahlerMeasure l)) /
      (1 + (Algebraic.algebraicDegree l : ℝ) + Real.log (Algebraic.mahlerMeasure l))) ^ 100 < l) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Continuous f ∧ HasCompactSupport f ∧
      Bernoulli.convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  have hB := Algebraic.complexity_pos hlalg (by linarith) hl1
  rw [← Algebraic.inv_complexity, inv_pow] at hsmall
  have hg : 1 - l < (Algebraic.complexity l ^ 100)⁻¹ := by linarith
  have hm := mul_lt_mul_of_pos_right hg (pow_pos hB 100)
  rw [inv_mul_cancel₀ (pow_ne_zero _ hB.ne')] at hm
  exact algebraic_bernoulli_continuous_density_of_gap hlalg hl0 hl1 (by linarith)

end LpSelfSimilar
