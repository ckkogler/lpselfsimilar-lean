module

public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
Measurability of actual variances of real-valued probability kernels. The proof
uses the defining centered-square integral, including laws whose second moment
is not finite. Bounds require only an almost-everywhere support interval.
-/

open MeasureTheory ProbabilityTheory

namespace LpSelfSimilar

lemma stronglyMeasurable_variance_kernel {Ω : Type*} [MeasurableSpace Ω]
    (κ : Kernel Ω ℝ) [IsSFiniteKernel κ] :
    StronglyMeasurable (fun ω ↦ variance (fun x : ℝ ↦ x) (κ ω)) := by
  have he : (fun ω ↦ variance (fun x : ℝ ↦ x) (κ ω)) =
      (fun ω ↦ ∫ x : ℝ, (x - ∫ z : ℝ, z ∂κ ω) ^ 2 ∂κ ω) := by
    funext ω
    exact variance_eq_integral (by fun_prop)
  rw [he]
  have hmean : StronglyMeasurable (fun ω ↦ ∫ x : ℝ, x ∂κ ω) :=
    stronglyMeasurable_id.integral_kernel
  exact (measurable_snd.stronglyMeasurable.sub
    (hmean.comp_measurable measurable_fst)).pow 2 |>.integral_kernel_prod_right'

lemma variance_kernel_le_radius_sq {Ω : Type*} [MeasurableSpace Ω]
    (κ : Kernel Ω ℝ) [IsMarkovKernel κ] (ω : Ω) {c R : ℝ}
    (hb : ∀ᵐ x ∂κ ω, |x - c| ≤ R) :
    variance (fun x : ℝ ↦ x) (κ ω) ≤ R ^ 2 := by
  have h : ∀ᵐ x ∂κ ω, x ∈ Set.Icc (c - R) (c + R) := hb.mono (fun x hx ↦ by
    have h := abs_le.mp hx
    constructor <;> linarith)
  have hv := variance_le_sq_of_bounded h (by fun_prop)
  convert hv using 1 <;> try rfl
  ring

/-- Uniform conditional support gives integrable conditional variances. -/
lemma integrable_variance_kernel_of_ae_radius {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (κ : Kernel Ω ℝ) [IsMarkovKernel κ]
    {c : Ω → ℝ} {R : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ᵐ x ∂κ ω, |x - c ω| ≤ R) :
    Integrable (fun ω ↦ variance (fun x : ℝ ↦ x) (κ ω)) P := by
  apply (integrable_const (R ^ 2)).mono'
    (stronglyMeasurable_variance_kernel κ).aestronglyMeasurable
  filter_upwards [hb] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (variance_nonneg _ _)]
  exact variance_kernel_le_radius_sq κ ω hω

end LpSelfSimilar
