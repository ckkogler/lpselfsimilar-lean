module

public import LpSelfSimilar.Probability.ConditionalMoments

@[expose] public section

/-!
Pushforward and scalar transformation rules for finite conditional moments.
All formulas hold on null fibers as well: the defining zero-denominator
convention is preserved. No measurability or injectivity is needed for finite
expectation pushforwards.
-/

namespace LpSelfSimilar.FiniteProbability

lemma expectation_map {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (g : α → β) (f : β → ℝ) :
    expectation (p.map g) (by simpa using hp.image g) f =
      expectation p hp (fun a ↦ f (g a)) :=
  Entropy.sum_marginal_mul p hp g f

lemma fiberVariance_map {α β γ : Type*} [DecidableEq γ] (p : PMF α)
    (hp : p.support.Finite) (g : α → β) (f : β → γ) (v : β → ℝ) (b : γ) :
    fiberVariance (p.map g) (by simpa using hp.image g) f v b =
      fiberVariance p hp (f ∘ g) (v ∘ g) b := by
  unfold fiberVariance
  simp only [expectation_map p hp g, PMF.map_comp, Function.comp_def]

lemma meanConditionalVariance_map {α β γ : Type*} [DecidableEq γ] (p : PMF α)
    (hp : p.support.Finite) (g : α → β) (f : β → γ) (v : β → ℝ) :
    meanConditionalVariance (p.map g) (by simpa using hp.image g) f v =
      meanConditionalVariance p hp (f ∘ g) (v ∘ g) := by
  unfold meanConditionalVariance
  rw [expectation_map p hp g]
  simp only [fiberVariance_map p hp g, Function.comp_apply]

lemma variance_const_mul {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (c : ℝ) (g : α → ℝ) :
    variance p hp (fun a ↦ c * g a) = c ^ 2 * variance p hp g := by
  rw [variance_eq_secondMoment_sub, variance_eq_secondMoment_sub]
  simp_rw [mul_pow, expectation_const_mul]
  ring

lemma fiberVariance_const_mul {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (c : ℝ) (g : α → ℝ) (b : β) :
    fiberVariance p hp f (fun a ↦ c * g a) b = c ^ 2 * fiberVariance p hp f g b := by
  have hfirst (a : α) : (if f a = b then c * g a else 0) =
      c * (if f a = b then g a else 0) := by split_ifs <;> ring
  have hsecond (a : α) : (if f a = b then (c * g a) ^ 2 else 0) =
      c ^ 2 * (if f a = b then g a ^ 2 else 0) := by split_ifs <;> ring
  unfold fiberVariance
  simp_rw [hfirst, hsecond, expectation_const_mul]
  ring

lemma meanConditionalVariance_const_mul {α β : Type*} [DecidableEq β] (p : PMF α)
    (hp : p.support.Finite) (f : α → β) (c : ℝ) (g : α → ℝ) :
    meanConditionalVariance p hp f (fun a ↦ c * g a) =
      c ^ 2 * meanConditionalVariance p hp f g := by
  unfold meanConditionalVariance
  simp_rw [fiberVariance_const_mul, expectation_const_mul]

end LpSelfSimilar.FiniteProbability
