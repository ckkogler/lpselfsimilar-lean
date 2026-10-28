module

public import LpSelfSimilar.Algebraic.PowerSelection

@[expose] public section

/-!
The selected algebraic power has a supported density in the exact space
L^(k/(k-1)) needed by the final residue convolution. Algebraicity of the power,
its quantitative gain and the finite-measure support comparison are all proved.
-/

open MeasureTheory Set Real
open LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Algebraic

theorem exists_power_density {l : ℝ} (hlalg : IsAlgebraic ℚ l)
    (hl0 : 1 / 2 ≤ l) (hl1 : l < 1)
    (hsmall : (1 - l) * complexity l ^ 100 < 2) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ f : ℝ → ℝ,
      (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      convolution (l ^ k) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      MemLp f (ENNReal.ofReal ((k : ℝ) / ((k : ℝ) - 1))) volume ∧
      (∀ x, x ∉ Icc (-(1 - l ^ k)⁻¹) (1 - l ^ k)⁻¹ → f x = 0) := by
  obtain ⟨k, hk, hθ0, hθ1, hθsmall, hexp⟩ := exists_smoothing_power hlalg hl0 hl1 hsmall
  obtain ⟨f, hf0, hf, hrep, hLp, hsupp⟩ :=
    higher_integrability (isAlgebraic_pow hlalg k) hθ0 hθ1 hθsmall
  refine ⟨k, hk, f, hf0, hf, hrep, ?_, hsupp⟩
  exact hLp.mono_exponent_of_measure_support_ne_top hsupp
    (by simp [Real.volume_Icc]) (ENNReal.ofReal_le_ofReal hexp)

end LpSelfSimilar.Algebraic
