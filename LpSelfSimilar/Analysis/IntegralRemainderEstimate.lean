module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic

@[expose] public section

/-!
L1 estimates for a finite expansion with an integrated remainder. Fubini and
all integrability requirements are explicit, so the estimate can be reused for
Gaussian variance Taylor expansions and other integral remainders.
-/

open MeasureTheory

namespace LpSelfSimilar

lemma integral_abs_integral_le {T : Type*} [MeasurableSpace T] {μ : Measure T}
    [SFinite μ] {G : T × ℝ → ℝ} (hG : Integrable G (μ.prod volume)) :
    (∫ x, |∫ t, G (t, x) ∂μ|) ≤ ∫ t, (∫ x, |G (t, x)|) ∂μ := by
  calc
    _ ≤ ∫ x, ∫ t, |G (t, x)| ∂μ := by
      apply integral_mono hG.integral_prod_right.abs hG.abs.integral_prod_right
      intro x
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun t ↦ G (t, x)) (μ := μ))
    _ = _ := integral_integral_swap hG.abs.swap

lemma integral_abs_finite_expansion_le {I T : Type*} [MeasurableSpace T]
    {μ : Measure T} [SFinite μ] (s : Finset I) (c : I → ℝ) (f : I → ℝ → ℝ)
    (hf : ∀ i ∈ s, Integrable (f i) volume) (d : ℝ) {G : T × ℝ → ℝ}
    (hG : Integrable G (μ.prod volume)) :
    (∫ x, |(∑ i ∈ s, c i * f i x) + d * ∫ t, G (t, x) ∂μ|) ≤
      (∑ i ∈ s, |c i| * ∫ x, |f i x|) + |d| * ∫ t, (∫ x, |G (t, x)|) ∂μ := by
  have hsum : Integrable (fun x ↦ ∑ i ∈ s, c i * f i x) volume := by
    exact integrable_finsetSum s (fun i hi ↦ (hf i hi).const_mul (c i))
  have hsumabs : Integrable (fun x ↦ ∑ i ∈ s, |c i| * |f i x|) volume := by
    exact integrable_finsetSum s (fun i hi ↦ (hf i hi).abs.const_mul |c i|)
  have hpoint (x : ℝ) : |(∑ i ∈ s, c i * f i x) + d * ∫ t, G (t, x) ∂μ| ≤
      (∑ i ∈ s, |c i| * |f i x|) + |d| * |∫ t, G (t, x) ∂μ| := by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    apply add_le_add _ le_rfl
    simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (f := fun i ↦ c i * f i x) (s := s)
  have h := integral_mono (hsum.add (hG.integral_prod_right.const_mul d)).abs
    (hsumabs.add (hG.integral_prod_right.abs.const_mul |d|)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hsumabs (hG.integral_prod_right.abs.const_mul |d|), integral_const_mul,
    integral_finsetSum s (fun i hi ↦ (hf i hi).abs.const_mul |c i|)] at h
  simp only [integral_const_mul] at h
  exact h.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (integral_abs_integral_le hG) (abs_nonneg d)))

end LpSelfSimilar
