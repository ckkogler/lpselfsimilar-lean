module

public import LpSelfSimilar.Bernoulli.FiniteLaw
public import LpSelfSimilar.Rational.DigitSeparation
public import LpSelfSimilar.Entropy.Finite

@[expose] public section

/-!
The elementary rational replacement of the entropy part of Lemma 3.6. The
distribution is the actual finite-digit law, and injectivity proved by modular
arithmetic makes its entropy exactly `n * log 2`, including `n = 0`.
-/

open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Rational

lemma digit_entropy {a b : ℕ} (ha : 2 ≤ a) (hb : 0 < b) (hab : a.Coprime b)
    (n : ℕ) :
    finiteEntropy (digitPMF ((a : ℝ) / b) n) (digitPMF_support_finite _ _) =
      (n : ℝ) * Real.log 2 := by
  unfold digitPMF
  rw [finiteEntropy_map_of_injective _ (Set.toFinite _) (digitSum_injective ha hb hab n),
    finiteEntropy_uniform]
  simp [Fintype.card_fun, Real.log_pow]

end LpSelfSimilar.Rational
