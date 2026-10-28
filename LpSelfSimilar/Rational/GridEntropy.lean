module

public import LpSelfSimilar.Rational.DigitEntropy
public import LpSelfSimilar.Entropy.Grid

@[expose] public section

/-!
The rational separation estimate resolves every digit atom at sufficiently fine
grid scales. Hence the shifted-grid entropy, not just the abstract word entropy,
is exactly `n log 2`. This is the small-scale endpoint needed in Lemma 3.7.
-/

open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Rational

theorem digit_gridEntropy {a b : ℕ} (ha : 2 ≤ a) (hb : 0 < b)
    (hab : a.Coprime b) (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hsep : s ≤ 2 / (b : ℝ) ^ (n - 1)) :
    gridEntropy (digitPMF ((a : ℝ) / b) n) (digitPMF_support_finite _ _) s =
      (n : ℝ) * Real.log 2 := by
  rw [gridEntropy_eq_of_separated _ _ hs]
  · exact digit_entropy ha hb hab n
  · intro x hx y hy hxy
    simp only [digitPMF, PMF.support_map] at hx hy
    obtain ⟨u, _, rfl⟩ := hx
    obtain ⟨v, _, rfl⟩ := hy
    apply hsep.trans
    apply digitSum_separation ha hb hab
    intro h
    exact hxy (congrArg (digitSum ((a : ℝ) / b)) h)

end LpSelfSimilar.Rational
