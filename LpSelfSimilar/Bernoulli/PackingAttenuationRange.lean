module

public import LpSelfSimilar.Bernoulli.DigitBandGrid

@[expose] public section

/-!
# The exact attenuation cap and derivative margin

Clipping after a nonnegative frequency loss preserves the sixteen-atom bound
`d_* = 1-sqrt(7/16)`. Thus the factor `52/(1-b)` used in differentiating the
independent Fourier product is strictly below eighty for every retained block.
-/

open Set

namespace LpSelfSimilar.Bernoulli

/-- Clipped digit attenuation retains the exact sixteen-atom cancellation cap. -/
theorem digitGridAttenuation_mem_exact_Icc (θ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) (j : ℝ) :
    digitGridAttenuation θ ε n j ∈ Icc 0 (1 - Real.sqrt (7 / 16)) := by
  have hd := digitBandCancellation_mem_Icc θ n j
  refine ⟨le_max_right _ _, max_le ?_ (hd.1.trans hd.2)⟩
  linarith [hd.2]

/-- The exact cancellation cap gives the strict factor-eighty derivative margin. -/
theorem derivative_cost_lt_eighty {b : ℝ} (hb : b ≤ 1 - Real.sqrt (7 / 16)) :
    (52 : ℝ) / (1 - b) < 80 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 16)
  have hs0 := Real.sqrt_nonneg (7 / 16 : ℝ)
  have hlo : (13 / 20 : ℝ) < Real.sqrt (7 / 16) := by nlinarith
  have hden : 0 < 1 - b := by linarith
  apply (div_lt_iff₀ hden).mpr
  linarith

end LpSelfSimilar.Bernoulli
