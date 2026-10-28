module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Tactic

@[expose] public section

/-!
A nonnegative representative for the L1 limit of nonnegative functions. The
Cauchy estimate is expressed using ordinary integrals, so callers need no
quotient-space infrastructure. Completeness and the closed positive cone of L1
supply the limit; taking the positive part changes it only on a null set.
-/

open MeasureTheory Filter
open scoped Topology

namespace LpSelfSimilar

lemma dist_toL1_eq_integral_abs_sub {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    dist (hf.toL1 f) (hg.toL1 g) = ∫ x, |f x - g x| ∂μ := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toL1, hg.coeFn_toL1] with x hfx hgx
  rw [hfx, hgx, Real.dist_eq]

/-- An integral Cauchy estimate tending to zero gives a pointwise nonnegative
integrable limit, with convergence in the actual L1 integral norm. -/
theorem exists_nonnegative_L1_limit {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → α → ℝ) (hF : ∀ n, Integrable (F n) μ)
    (hF0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ F n x) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 0))
    (hC : ∀ n m, n ≤ m → (∫ x, |F n x - F m x| ∂μ) ≤ b n) :
    ∃ f : α → ℝ, Integrable f μ ∧ (∀ x, 0 ≤ f x) ∧
      Tendsto (fun n ↦ ∫ x, |F n x - f x| ∂μ) atTop (𝓝 0) := by
  let u (n : ℕ) : α →₁[μ] ℝ := (hF n).toL1 (F n)
  have hcu : CauchySeq u := cauchySeq_of_le_tendsto_0' b (by
    intro n m hnm
    rw [dist_toL1_eq_integral_abs_sub]
    exact hC n m hnm) hb
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcu
  have hu (n : ℕ) : 0 ≤ u n := by
    apply (Lp.coeFn_nonneg (u n)).mp
    filter_upwards [(hF n).coeFn_toL1, hF0 n] with x hx h0
    change 0 ≤ (u n) x
    exact h0.trans_eq hx.symm
  have hv0 : 0 ≤ v := ge_of_tendsto' hv hu
  have hv0ae := (Lp.coeFn_nonneg v).mpr hv0
  let f : α → ℝ := fun x ↦ max (v x) 0
  have hfv : f =ᵐ[μ] v := by
    filter_upwards [hv0ae] with x hx
    exact max_eq_left hx
  have hf : Integrable f μ := (L1.integrable_coeFn v).congr hfv.symm
  refine ⟨f, hf, fun x ↦ le_max_right _ _, ?_⟩
  have he (n : ℕ) : (∫ x, |F n x - f x| ∂μ) = dist (u n) v := by
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [(hF n).coeFn_toL1, hfv] with x hx hfx
    change |F n x - f x| = dist ((u n) x) (v x)
    rw [hx, hfx, Real.dist_eq]
  simp_rw [he]
  exact (tendsto_iff_dist_tendsto_zero).mp hv

end LpSelfSimilar
