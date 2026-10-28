module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

@[expose] public section

/-!
Square-root Jensen inequalities for probability measures. Integrability of the
square root is derived from integrability of the nonnegative input, and hence
is not left as an extra analytic hypothesis at applications.
-/

open MeasureTheory Set Real

namespace LpSelfSimilar

lemma integrable_sqrt_of_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    Integrable (fun x ↦ Real.sqrt (f x)) μ := by
  apply (hf.add (integrable_const (1 : ℝ))).mono'
    (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  filter_upwards [hn] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  change Real.sqrt (f x) ≤ f x + 1
  have hs := Real.sq_sqrt hx
  nlinarith [sq_nonneg (Real.sqrt (f x) - 1 / 2)]

lemma integral_sqrt_le_sqrt_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (∫ x, Real.sqrt (f x) ∂μ) ≤ Real.sqrt (∫ x, f x ∂μ) :=
  Real.strictConcaveOn_sqrt.concaveOn.le_map_integral Real.continuous_sqrt.continuousOn
    isClosed_Ici hn hf (integrable_sqrt_of_nonneg hf hn)

/-- The elementary numerical comparison giving the constant ten in Lemma 3.5. -/
lemma four_sqrt_sqrt_div_quarter_le {v s : ℝ} (hv : 0 ≤ v) (hs : 0 < s) :
    4 * Real.sqrt (Real.sqrt (2 * v) / (s / 4)) ≤
      10 * Real.sqrt (Real.sqrt (v / s ^ 2)) := by
  have hdiv : Real.sqrt (v / s ^ 2) = Real.sqrt v / s := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ Real.sqrt v / s)).mp
    rw [Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt hv]
  have hmul : Real.sqrt (2 * v) = Real.sqrt 2 * Real.sqrt v := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ Real.sqrt 2 * Real.sqrt v)).mp
    rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hv]
  have hnum : Real.sqrt 2 ≤ 25 / 16 := by
    have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg 2]
  have hlink : Real.sqrt (Real.sqrt (2 * v) / (s / 4)) ^ 2 =
      4 * Real.sqrt 2 * Real.sqrt (Real.sqrt (v / s ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (Real.sqrt_nonneg _), hdiv, hmul]
    field_simp
  have hm := mul_nonneg (sub_nonneg.mpr hnum)
    (sq_nonneg (Real.sqrt (Real.sqrt (v / s ^ 2))))
  nlinarith [Real.sqrt_nonneg (Real.sqrt (2 * v) / (s / 4)),
    Real.sqrt_nonneg (Real.sqrt (v / s ^ 2))]

end LpSelfSimilar
