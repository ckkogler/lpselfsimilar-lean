module

public import Mathlib.Tactic

@[expose] public section

/-!
The scalar budget for effective Gaussian detail. The explicit scale count and
a small logarithmic contraction make the expected block variance large enough
for all derivative orders at most ten times the logarithmic scale.
-/

namespace LpSelfSimilar

lemma effective_variance_budget {B χ ε c L M K : ℝ}
    (hB : 0 < B) (hχ : 0 < χ) (hM : 0 ≤ M)
    (hsmall : χ * B ^ 9 ≤ ε ^ 2 * c / 100000000)
    (hcount : L / (2000 * B ^ 2) ≤ M) (hK : K ≤ 10 * L) :
    1001 * K ≤ M * (ε ^ 2 / 4 * (c / (χ * B ^ 7))) := by
  have hL : L ≤ M * (2000 * B ^ 2) :=
    (div_le_iff₀ (by positivity : 0 < 2000 * B ^ 2)).mp hcount
  have horder : K ≤ 20000 * B ^ 2 * M := by linarith
  have hs : 40040000 * χ * B ^ 9 ≤ ε ^ 2 * c := by
    have hp : 0 ≤ χ * B ^ 9 := by positivity
    linarith
  have h1 := mul_le_mul_of_nonneg_right horder
    (by positivity : 0 ≤ 1001 * χ * B ^ 7)
  have h2 := mul_le_mul_of_nonneg_left hs hM
  have hh : 1001 * K * (χ * B ^ 7) ≤ M * ε ^ 2 * c / 4 := by
    nlinarith [mul_nonneg hM (by positivity : 0 ≤ χ * B ^ 9)]
  have he : M * (ε ^ 2 / 4 * (c / (χ * B ^ 7))) =
      (M * ε ^ 2 * c / 4) / (χ * B ^ 7) := by ring
  rw [he]
  exact (le_div_iff₀ (by positivity : 0 < χ * B ^ 7)).mpr hh

end LpSelfSimilar
