module

public import LpSelfSimilar.Rational.PowerSelection

@[expose] public section

/-!
The selected rational power has a supported density in the precise space
L^(k/(k-1)) needed for the final k-fold convolution. Reduction under powers
and finite-support exponent comparison are supplied here, not assumed.
-/

open MeasureTheory Set Real
open LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Rational

theorem exists_power_density {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) (hab : a.Coprime b)
    (hl0 : 1 / 2 ≤ (a : ℝ) / b) (hl1 : (a : ℝ) / b < 1)
    (hsmall : (1 - (a : ℝ) / b) * complexity b ^ 50 ≤ powerThreshold) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ f : ℝ → ℝ,
      (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      convolution (((a : ℝ) / b) ^ k) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      MemLp f (ENNReal.ofReal ((k : ℝ) / ((k : ℝ) - 1))) volume ∧
      (∀ x, x ∉ Icc (-(1 - ((a : ℝ) / b) ^ k)⁻¹)
        (1 - ((a : ℝ) / b) ^ k)⁻¹ → f x = 0) := by
  obtain ⟨k, hk, hθ0, hθ1, hθsmall, hexp⟩ := exists_smoothing_power ha hb hl0 hl1 hsmall
  have hk1 : 1 ≤ k := by omega
  have haP : 2 ≤ a ^ k := ha.trans (by
    simpa using pow_le_pow_right₀ (show 1 ≤ a by omega) hk1)
  have hbP : 2 ≤ b ^ k := hb.trans (by
    simpa using pow_le_pow_right₀ (show 1 ≤ b by omega) hk1)
  have he := real_ratio_pow a b k
  obtain ⟨f, hf0, hf, hrep, hLp, hsupp⟩ := higher_integrability haP hbP (reduced_power hab)
    (he ▸ hθ0.le) (he ▸ hθ1) (he ▸ hθsmall)
  rw [← he] at hrep hLp hsupp
  refine ⟨k, hk, f, hf0, hf, hrep, ?_, hsupp⟩
  exact hLp.mono_exponent_of_measure_support_ne_top hsupp
    (by simp [Real.volume_Icc]) (ENNReal.ofReal_le_ofReal hexp)

end LpSelfSimilar.Rational
