module

public import LpSelfSimilar.Rational.PowerIntegrability
public import LpSelfSimilar.Bernoulli.ContinuousDensity

@[expose] public section

/-!
Corollary 1.3 by the rational route. One absolute constant is selected before
both integer parameters. The exact logarithmic exponent fifty implies the
proved power threshold; rational Proposition 3.1 and the residue convolution
then supply the continuous compactly supported density.
-/

open MeasureTheory Real

namespace LpSelfSimilar

/-- Corollary 1.3: rational Bernoulli convolutions sufficiently close to one
have nonnegative continuous compactly supported densities. All analytic and
arithmetic inputs are proved in the library; the constant is uniform in p,q. -/
theorem bernoulli_convolution_continuous_density :
    ∃ c : ℝ, 0 < c ∧ ∀ (p q : ℕ), 0 < p → 0 < q → p.Coprime q →
      (1 : ℝ) / 2 < 1 - (p : ℝ) / (q : ℝ) → 1 - (p : ℝ) / (q : ℝ) < 1 →
      (p : ℝ) ≤ c * (q : ℝ) / (Real.log (q : ℝ)) ^ 50 →
      ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Continuous f ∧ HasCompactSupport f ∧
        Bernoulli.convolution (1 - (p : ℝ) / (q : ℝ)) =
          volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  obtain ⟨c, hc, hbound⟩ := Rational.exists_uniform_constant_for_complexity
    Rational.powerThreshold Rational.powerThreshold_pos
  refine ⟨c, hc, ?_⟩
  intro p q _hp hq hpq hhalf hone hsmall
  obtain ⟨ha, hb, hab, he⟩ := Rational.reduced_gap_parameter hq hpq hhalf hone
  have hB := hbound p q (by omega) hsmall
  have hs : (1 - (((q - p : ℕ) : ℝ) / q)) * Rational.complexity q ^ 50 ≤
      Rational.powerThreshold := by
    rw [← he]
    simpa only [sub_sub_cancel] using hB.le
  obtain ⟨k, hk, f, hfn, hf, hrep, hLp, _hsupp⟩ := Rational.exists_power_density
    ha (by omega) hab (he ▸ hhalf.le) (he ▸ hone) hs
  rw [← he] at hrep
  exact Bernoulli.continuous_density_of_power_memLp (by linarith) hone hk hf hfn hrep hLp

end LpSelfSimilar
