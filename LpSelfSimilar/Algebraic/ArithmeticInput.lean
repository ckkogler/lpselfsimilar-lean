module

public import LpSelfSimilar.Algebraic.DigitEntropy
public import LpSelfSimilar.Algebraic.GridEntropy
public import LpSelfSimilar.Algebraic.GapEstimate

@[expose] public section

/-!
Revised Lemma 3.6: all four arithmetic inputs at their exact constants.

The degree and Mahler measure are canonical. Separation concerns distinct actual
atoms, not distinct words. The entropy bound uses an elementary expanding-conjugate
and sparse-digit proof in the unit case. Every finite word length, including zero,
is covered, and fine-grid entropy inherits the proved actual-law lower bound.
-/

open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Algebraic

/-- All four assertions of (3.8), with the paper's hypotheses and constants. -/
theorem arithmetic_input {r : ℝ} (hr : IsAlgebraic ℚ r)
    (hr0 : (1 : ℝ) / 2 < r) (hr1 : r < 1) (n : ℕ) :
    3 ≤ complexity r ∧
    (∀ a ∈ (digitPMF r n).support, ∀ b ∈ (digitPMF r n).support,
      a ≠ b → Real.exp (-complexity r * n) ≤ |a - b|) ∧
    (n : ℝ) / (8 * complexity r) ≤
      finiteEntropy (digitPMF r n) (digitPMF_support_finite _ _) ∧
    Real.log (1 / (1 - r)) ≤ complexity r := by
  have hrp : 0 < r := by linarith
  refine ⟨three_le_complexity hr hrp hr1, ?_,
    digit_entropy_ge_length_div_eight_complexity hr hrp hr1 n, ?_⟩
  · intro a ha b hb hab
    exact digitPMF_support_separation hr hrp hr1 n ha hb hab
  · exact log_inverse_gap_le_complexity hr hrp hr1

/-- The exact entropy lower bound persists at every scale resolving distinct
actual atoms, without assuming full digit-word injectivity. -/
theorem digit_gridEntropy_ge_length_div_eight_complexity {r : ℝ} (hr : IsAlgebraic ℚ r)
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hsep : s ≤ Real.exp (-complexity r * n)) :
    (n : ℝ) / (8 * complexity r) ≤
      gridEntropy (digitPMF r n) (digitPMF_support_finite _ _) s := by
  rw [digit_gridEntropy_eq_entropy hr hr0 hr1 n hs hsep]
  exact digit_entropy_ge_length_div_eight_complexity hr hr0 hr1 n

end LpSelfSimilar.Algebraic
