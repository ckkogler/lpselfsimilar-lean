module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Derivative bounds for finite products

The binomial Leibniz formula retains the exact power of the sum of derivative
costs. In particular, the second derivative incurs no additional factor two.
The majorants may vary with the evaluation point; only differentiability is
required in a neighbourhood. This form applies both to cosine factors and to
conditional characteristic functions.
-/

open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- Product derivative costs add, while the undifferentiated majorants multiply. -/
theorem norm_iteratedDeriv_finset_prod_le {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (v w : ι → ℝ) (n : ℕ) (x : ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hf : ∀ i ∈ s, ContDiffAt ℝ n (f i) x)
    (hb : ∀ i ∈ s, ∀ k ≤ n, ‖iteratedDeriv k (f i) x‖ ≤ w i ^ k * v i) :
    ∀ k ≤ n, ‖iteratedDeriv k (fun y ↦ ∏ i ∈ s, f i y) x‖ ≤
      (∑ i ∈ s, w i) ^ k * ∏ i ∈ s, v i := by
  classical
  revert hv hw hf hb
  induction s using Finset.induction_on with
  | empty =>
      intro hv hw hf hb k hk
      cases k <;> simp [iteratedDeriv_const]
  | @insert a s ha ih =>
      intro hv hw hf hb k hk
      have hva : 0 ≤ v a := hv a (Finset.mem_insert_self _ _)
      have hwa : 0 ≤ w a := hw a (Finset.mem_insert_self _ _)
      have hvs : ∀ i ∈ s, 0 ≤ v i := fun i hi ↦ hv i (Finset.mem_insert_of_mem hi)
      have hws : ∀ i ∈ s, 0 ≤ w i := fun i hi ↦ hw i (Finset.mem_insert_of_mem hi)
      have hfs : ∀ i ∈ s, ContDiffAt ℝ n (f i) x :=
        fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
      have hbs := ih hvs hws hfs (fun i hi ↦ hb i (Finset.mem_insert_of_mem hi))
      have hfa : ContDiffAt ℝ k (f a) x :=
        (hf a (Finset.mem_insert_self _ _)).of_le (by exact_mod_cast hk)
      have hfp : ContDiffAt ℝ k (fun y ↦ ∏ i ∈ s, f i y) x :=
        (contDiffAt_prod hfs).of_le (by exact_mod_cast hk)
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [iteratedDeriv_fun_mul hfa hfp]
      calc
        _ ≤ ∑ j ∈ Finset.range (k + 1),
            ‖(k.choose j : ℂ) * iteratedDeriv j (f a) x *
              iteratedDeriv (k - j) (fun y ↦ ∏ i ∈ s, f i y) x‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.range (k + 1),
            (k.choose j : ℝ) * (w a ^ j * v a) *
              ((∑ i ∈ s, w i) ^ (k - j) * ∏ i ∈ s, v i) := by
          apply Finset.sum_le_sum
          intro j hj
          have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          simp only [norm_mul, Complex.norm_natCast]
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left
              (hb a (Finset.mem_insert_self _ _) j (hjk.trans hk)) (by positivity))
            (hbs (k - j) ((Nat.sub_le k j).trans hk))
            (norm_nonneg _) (by positivity)
        _ = (w a + ∑ i ∈ s, w i) ^ k * (v a * ∏ i ∈ s, v i) := by
          rw [add_pow, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring

end LpSelfSimilar.Analysis
