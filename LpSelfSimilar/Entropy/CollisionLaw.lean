module

public import LpSelfSimilar.Entropy.Collision
public import LpSelfSimilar.Entropy.Conditioning
public import LpSelfSimilar.Probability.FiniteMoments

@[expose] public section

/-!
Collision probability is the probability that two independent samples agree.
The finite weighted formulas here are expectations for the actual PMF measure,
as proved in `Probability/FiniteMoments`. They apply also after any statistic.
-/

open LpSelfSimilar.FiniteProbability
open scoped ENNReal

namespace LpSelfSimilar.Entropy

lemma expectation_same_eq_marginal {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (a : α) :
    expectation p hp (fun b ↦ if f a = f b then (1 : ℝ) else 0) =
      ((p.map f) (f a)).toReal := by
  rw [marginal_toReal_eq_finite_sum p hp f]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : f a = f b <;> simp [h, Ne.symm, eq_comm]

lemma collisionProbability_map_eq_expectation_same {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) :
    collisionProbability (p.map f) (by simpa using hp.image f) =
      expectation p hp (fun a ↦ expectation p hp (fun b ↦ if f a = f b then (1 : ℝ) else 0)) := by
  simp_rw [expectation_same_eq_marginal p hp f]
  have h := sum_marginal_mul p hp f (fun b ↦ ((p.map f) b).toReal)
  simpa only [collisionProbability, expectation, pow_two] using h

lemma disagreement_eq_expectation_ne {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) :
    1 - collisionProbability (p.map f) (by simpa using hp.image f) =
      expectation p hp (fun a ↦ expectation p hp (fun b ↦ if f a ≠ f b then (1 : ℝ) else 0)) := by
  have he (a b : α) : (if f a ≠ f b then (1 : ℝ) else 0) =
      1 - (if f a = f b then 1 else 0) := by split_ifs <;> simp_all
  simp_rw [he, expectation_sub, expectation_const]
  rw [collisionProbability_map_eq_expectation_same]

end LpSelfSimilar.Entropy
