module

public import LpSelfSimilar.Analysis.WeightedProductDerivatives

@[expose] public section

/-!
# Derivatives under finite independent label averages

Recursing over the finite family decomposes a label tuple into its first label
and its remaining labels. The two-factor averaged Leibniz estimate then gives
an exact power of the sum of derivative costs. No pointwise attenuation bound
is used, and empty families and zero label weights are included.
-/

open scoped BigOperators

namespace LpSelfSimilar.Analysis

/-- Independent finite averages multiply derivative majorants and add their costs. -/
theorem sum_norm_iteratedDeriv_independent_prod_le (m n : ℕ) (x : ℝ)
    {Ω : Fin m → Type*} [∀ i, Fintype (Ω i)]
    (p : (i : Fin m) → Ω i → ℝ) (f : (i : Fin m) → Ω i → ℝ → ℂ)
    (v w : Fin m → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i)
    (hf : ∀ i a, ContDiffAt ℝ n (f i a) x)
    (hb : ∀ i, ∀ k ≤ n, (∑ a, p i a * ‖iteratedDeriv k (f i a) x‖) ≤ w i ^ k * v i) :
    ∀ k ≤ n, (∑ ω : (i : Fin m) → Ω i, (∏ i, p i (ω i)) *
      ‖iteratedDeriv k (fun y ↦ ∏ i, f i (ω i) y) x‖) ≤
        (∑ i, w i) ^ k * ∏ i, v i := by
  classical
  revert hb hf hw hv hp w v f p Ω
  induction m with
  | zero =>
      intro Ω inst p f v w hp hv hw hf hb k hk
      cases k <;> simp [iteratedDeriv_const]
  | succ m ih =>
      intro Ω inst p f v w hp hv hw hf hb k hk
      have ht := ih (fun i a ↦ p i.succ a) (fun i a ↦ f i.succ a)
        (fun i ↦ v i.succ) (fun i ↦ w i.succ)
        (fun i a ↦ hp i.succ a) (fun i ↦ hv i.succ) (fun i ↦ hw i.succ)
        (fun i a ↦ hf i.succ a) (fun i ↦ hb i.succ)
      have h := sum_norm_iteratedDeriv_mul_le (p 0)
        (fun ω : (i : Fin m) → Ω i.succ ↦ ∏ i, p i.succ (ω i)) (f 0)
        (fun ω y ↦ ∏ i : Fin m, f i.succ (ω i) y)
        (hv 0) (Finset.prod_nonneg (fun i hi ↦ hv i.succ))
        (hw 0) (Finset.sum_nonneg (fun i hi ↦ hw i.succ))
        (hp 0) (fun ω ↦ Finset.prod_nonneg (fun i hi ↦ hp i.succ (ω i)))
        n x (hf 0) (fun ω ↦ contDiffAt_prod (fun i hi ↦ hf i.succ (ω i)))
        (hb 0) ht k hk
      have he : (∑ ω : (i : Fin (m + 1)) → Ω i, (∏ i, p i (ω i)) *
          ‖iteratedDeriv k (fun y ↦ ∏ i, f i (ω i) y) x‖) =
          ∑ a, ∑ b : (i : Fin m) → Ω i.succ,
            p 0 a * (∏ i, p i.succ (b i)) *
              ‖iteratedDeriv k (fun y ↦ f 0 a y * ∏ i, f i.succ (b i) y) x‖ := by
        rw [← (Fin.consEquiv Ω).sum_comp (fun ω : (i : Fin (m + 1)) → Ω i ↦
          (∏ i, p i (ω i)) * ‖iteratedDeriv k (fun y ↦ ∏ i, f i (ω i) y) x‖)]
        simp only [Fintype.sum_prod_type, Fin.consEquiv_apply, Fin.prod_univ_succ,
          Fin.cons_zero, Fin.cons_succ]
      rw [he, Fin.sum_univ_succ, Fin.prod_univ_succ]
      exact h

end LpSelfSimilar.Analysis
