module

public import LpSelfSimilar.Analysis.ProductDerivativeBounds
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-!
# Derivative bounds averaged over independent finite labels

Leibniz terms are averaged before applying the majorants. Thus an attenuation
bound is required only in mean. Nonnegative finite weights suffice; normalization
is supplied by the actual probability mass functions at the application site.
-/

open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- Independent finite averages obey the same exact two-factor derivative-cost bound. -/
theorem sum_norm_iteratedDeriv_mul_le {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (q : β → ℝ) (f : α → ℝ → ℂ) (g : β → ℝ → ℂ)
    {u v w z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hz : 0 ≤ z)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b) (n : ℕ) (x : ℝ)
    (hf : ∀ a, ContDiffAt ℝ n (f a) x) (hg : ∀ b, ContDiffAt ℝ n (g b) x)
    (hfb : ∀ j ≤ n, (∑ a, p a * ‖iteratedDeriv j (f a) x‖) ≤ w ^ j * u)
    (hgb : ∀ j ≤ n, (∑ b, q b * ‖iteratedDeriv j (g b) x‖) ≤ z ^ j * v)
    (k : ℕ) (hk : k ≤ n) :
    (∑ a, ∑ b, p a * q b * ‖iteratedDeriv k (fun y ↦ f a y * g b y) x‖) ≤
      (w + z) ^ k * (u * v) := by
  classical
  have hb (a : α) (b : β) :
      ‖iteratedDeriv k (fun y ↦ f a y * g b y) x‖ ≤
        ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
          ‖iteratedDeriv j (f a) x‖ * ‖iteratedDeriv (k - j) (g b) x‖ := by
    rw [iteratedDeriv_fun_mul ((hf a).of_le (by exact_mod_cast hk))
      ((hg b).of_le (by exact_mod_cast hk))]
    simpa only [norm_mul, Complex.norm_natCast] using norm_sum_le (Finset.range (k + 1))
      (fun j ↦ (k.choose j : ℂ) * iteratedDeriv j (f a) x *
        iteratedDeriv (k - j) (g b) x)
  calc
    _ ≤ ∑ a, ∑ b, p a * q b *
        ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
          ‖iteratedDeriv j (f a) x‖ * ‖iteratedDeriv (k - j) (g b) x‖ := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb'
      exact mul_le_mul_of_nonneg_left (hb a b) (mul_nonneg (hp a) (hq b))
    _ = ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
        (∑ a, p a * ‖iteratedDeriv j (f a) x‖) *
        (∑ b, q b * ‖iteratedDeriv (k - j) (g b) x‖) := by
      simp_rw [Finset.mul_sum]
      conv_lhs =>
        arg 2
        ext a
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb'
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ ∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (w ^ j * u) * (z ^ (k - j) * v) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfb j (hjk.trans hk)) (by positivity))
        (hgb (k - j) ((Nat.sub_le k j).trans hk))
        (Finset.sum_nonneg (fun b hb' ↦ mul_nonneg (hq b) (norm_nonneg _)))
        (by positivity)
    _ = _ := by
      rw [add_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

end LpSelfSimilar.Analysis
