module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
L1 convergence implies convergence against bounded measurable test functions.
The explicit real integral estimate will identify the Gaussian L1 limit with
its weak measure limit without assuming a density representation.
-/

open MeasureTheory Filter
open scoped Topology

namespace LpSelfSimilar

lemma integral_abs_sub_triangle {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, |f x - h x| ∂μ) ≤ (∫ x, |f x - g x| ∂μ) + ∫ x, |g x - h x| ∂μ := by
  have hi := integral_add (hf.sub hg).abs (hg.sub hh).abs
  simp only [Pi.sub_apply] at hi
  rw [← hi]
  apply integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
  intro x
  change |f x - h x| ≤ |f x - g x| + |g x - h x|
  exact abs_sub_le _ _ _

lemma integral_abs_sub_le_of_L1_limit {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} (hF : ∀ n, Integrable (F n) μ)
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hlim : Tendsto (fun n ↦ ∫ x, |F n x - f x| ∂μ) atTop (𝓝 0))
    {C : ℝ} (hC : ∀ n, (∫ x, |F n x - g x| ∂μ) ≤ C) :
    (∫ x, |f x - g x| ∂μ) ≤ C := by
  have hbound (n : ℕ) : (∫ x, |f x - g x| ∂μ) ≤ (∫ x, |F n x - f x| ∂μ) + C := by
    have h := integral_abs_sub_triangle hf (hF n) hg
    rw [show (∫ x, |f x - F n x| ∂μ) = ∫ x, |F n x - f x| ∂μ by
      simp only [abs_sub_comm]] at h
    exact h.trans (add_le_add le_rfl (hC n))
  have ht : Tendsto (fun n ↦ (∫ x, |F n x - f x| ∂μ) + C) atTop (𝓝 C) := by
    simpa only [zero_add] using hlim.add_const C
  exact ge_of_tendsto' ht hbound

lemma abs_integral_bounded_mul_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g φ : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hφ : AEStronglyMeasurable φ μ) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ M) :
    |(∫ x, φ x * f x ∂μ) - ∫ x, φ x * g x ∂μ| ≤ M * ∫ x, |f x - g x| ∂μ := by
  have hif := hf.bdd_mul hφ hb
  have hig := hg.bdd_mul hφ hb
  rw [← integral_sub hif hig, ← integral_const_mul]
  apply (show |∫ x, φ x * f x - φ x * g x ∂μ| ≤
    ∫ x, |φ x * f x - φ x * g x| ∂μ from by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x ↦ φ x * f x - φ x * g x) (μ := μ)).trans
  apply integral_mono_ae (hif.sub hig).abs ((hf.sub hg).abs.const_mul M)
  filter_upwards [hb] with x hx
  change |φ x * f x - φ x * g x| ≤ M * |f x - g x|
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hx) (abs_nonneg _)

/-- Convergence tested against any bounded measurable real function. -/
theorem tendsto_integral_bounded_mul_of_L1 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} (hF : ∀ n, Integrable (F n) μ)
    {f φ : α → ℝ} (hf : Integrable f μ) (hφ : AEStronglyMeasurable φ μ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ x ∂μ, ‖φ x‖ ≤ M)
    (hlim : Tendsto (fun n ↦ ∫ x, |F n x - f x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, φ x * F n x ∂μ) atTop (𝓝 (∫ x, φ x * f x ∂μ)) := by
  apply (tendsto_iff_dist_tendsto_zero).mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun n ↦ abs_nonneg _)
    (fun n ↦ abs_integral_bounded_mul_sub_le (hF n) hf hφ hM hb)
    (by simpa only [mul_zero] using hlim.const_mul M)

end LpSelfSimilar
