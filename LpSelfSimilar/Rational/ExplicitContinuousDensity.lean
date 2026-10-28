module

public import LpSelfSimilar.Algebraic.ContinuousDensity
public import LpSelfSimilar.Algebraic.RationalIdentification
public import LpSelfSimilar.Rational.ExplicitComplexity
public import LpSelfSimilar.Rational.Parameters

@[expose] public section

/-!
Revised Corollary 1.3, with coefficient 3 and exponent 100 exactly as printed.
The rational parameter is reduced explicitly, including positivity and the small
denominator exclusions. Canonical algebraic complexity equals rational complexity;
the full proved algebraic theorem supplies the actual continuous density.
The historical exponent-fifty theorem and its public name are preserved.
-/

open MeasureTheory Real

namespace LpSelfSimilar

/-- **Corollary 1.3 of On Lp density of self similar measures and Bernoulli convolutions**, with the exact parameter condition.
All divisions and logarithms are real; the conclusion concerns the actual
independent fair-sign Bernoulli convolution. -/
theorem rational_bernoulli_convolution_continuous_density_explicit
    (p q : ℕ) (_hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q)
    (hhalf : (1 : ℝ) / 2 < 1 - (p : ℝ) / (q : ℝ))
    (hone : 1 - (p : ℝ) / (q : ℝ) < 1)
    (hsmall : (p : ℝ) ≤ (q : ℝ) / (3 * Real.log (q : ℝ)) ^ 100) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Continuous f ∧ HasCompactSupport f ∧
      Bernoulli.convolution (1 - (p : ℝ) / (q : ℝ)) =
        volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  obtain ⟨ha, hb, hab, he⟩ := Rational.reduced_gap_parameter hq hpq hhalf hone
  have hlt : q - p < q := by
    exact_mod_cast (div_lt_one (by positivity : (0 : ℝ) < q)).mp (he ▸ hone)
  have hB : Algebraic.complexity (1 - (p : ℝ) / q) = Rational.complexity q := by
    rw [he, Algebraic.complexity_rat_div hq hab hlt]
  have hlalg : IsAlgebraic ℚ (1 - (p : ℝ) / (q : ℝ)) := by
    simpa using (isAlgebraic_ratCast ℚ (1 - (p : ℚ) / q) :
      IsAlgebraic ℚ ((1 - (p : ℚ) / q : ℚ) : ℝ))
  apply algebraic_bernoulli_continuous_density_of_gap hlalg hhalf hone
  rw [hB, sub_sub_cancel]
  exact (Rational.gap_complexity_power_one_hundred_le hb hsmall).trans_lt (by norm_num)

end LpSelfSimilar
