module

public import LpSelfSimilar.Analysis.SqrtAverages

@[expose] public section

/-!
The fourth-root integral estimate used to convert integrated entropy increments
into a lower bound on integrated conditional variance. It is Jensen's inequality
for the normalized finite measure, with the normalization explicitly canceled.
-/

open MeasureTheory Set Real

namespace LpSelfSimilar

lemma integral_fourthRoot_pow_four_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫ x, Real.sqrt (Real.sqrt (f x)) ∂μ) ^ 4 ≤
      μ.real univ ^ 3 * ∫ x, f x ∂μ := by
  by_cases hz : μ = 0
  · simp [hz]
  letI : NeZero μ := ⟨hz⟩
  have hi := integrable_sqrt_of_nonneg hf hn
  have hin := ae_of_all μ (fun x ↦ Real.sqrt_nonneg (f x))
  have hi2 := integrable_sqrt_of_nonneg hi hin
  have h1 := Real.strictConcaveOn_sqrt.concaveOn.le_map_average
    Real.continuous_sqrt.continuousOn isClosed_Ici hn hf hi
  have h2 := Real.strictConcaveOn_sqrt.concaveOn.le_map_average
    Real.continuous_sqrt.continuousOn isClosed_Ici hin hi hi2
  have h := h2.trans (Real.sqrt_le_sqrt h1)
  simp only [average_eq, smul_eq_mul] at h
  have hm : 0 < μ.real univ := measureReal_univ_pos
  have hfn : 0 ≤ ∫ x, f x ∂μ := integral_nonneg_of_ae hn
  have hrn : 0 ≤ ∫ x, Real.sqrt (Real.sqrt (f x)) ∂μ :=
    integral_nonneg (fun _ ↦ Real.sqrt_nonneg _)
  have hp := pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hm.le) hrn) h 4
  have he : Real.sqrt (Real.sqrt ((μ.real univ)⁻¹ * ∫ x, f x ∂μ)) ^ 4 =
      (μ.real univ)⁻¹ * ∫ x, f x ∂μ := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
  rw [he] at hp
  have hh := mul_le_mul_of_nonneg_left hp (pow_nonneg hm.le 4)
  field_simp at hh
  nlinarith

end LpSelfSimilar
