module

public import LpSelfSimilar.Analysis.NonnegativeL1Limit

@[expose] public section

/-!
# Measurable limits of signed L1 Cauchy sequences

Completeness of L1 applies before any positivity of the approximating kernels
is known. The canonical Lp representative is measurable, and the conclusion
uses the actual integral of the absolute difference. Positivity of a density
will be proved later from its identification with the probability measure.
-/

open MeasureTheory Filter
open scoped Topology

namespace LpSelfSimilar.Analysis

/-- An integral Cauchy bound gives a measurable integrable limit, without a sign assumption. -/
theorem exists_measurable_L1_limit {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (F : ℕ → α → ℝ) (hF : ∀ n, Integrable (F n) μ) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 0))
    (hC : ∀ n m, n ≤ m → (∫ x, |F n x - F m x| ∂μ) ≤ b n) :
    ∃ f : α → ℝ, Measurable f ∧ Integrable f μ ∧
      Tendsto (fun n => ∫ x, |F n x - f x| ∂μ) atTop (𝓝 0) := by
  let u (n : ℕ) : α →₁[μ] ℝ := (hF n).toL1 (F n)
  have hcu : CauchySeq u := cauchySeq_of_le_tendsto_0' b (by
    intro n m hnm
    rw [dist_toL1_eq_integral_abs_sub]
    exact hC n m hnm) hb
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcu
  refine ⟨v, (Lp.stronglyMeasurable v).measurable, L1.integrable_coeFn v, ?_⟩
  have he (n : ℕ) : (∫ x, |F n x - v x| ∂μ) = dist (u n) v := by
    rw [L1.dist_eq_integral_dist]
    apply integral_congr_ae
    filter_upwards [(hF n).coeFn_toL1] with x hx
    change |F n x - v x| = dist ((u n) x) (v x)
    rw [hx, Real.dist_eq]
  simp_rw [he]
  exact (tendsto_iff_dist_tendsto_zero).mp hv

end LpSelfSimilar.Analysis
