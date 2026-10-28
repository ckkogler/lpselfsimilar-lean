module

public import LpSelfSimilar.Analysis.VectorConvolutionMixture
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-!
# Affine laws convolved with rescaled kernels

The spatial normalization of each conditional law is transferred to its
convolution integral. Both the scale Jacobian and the label-dependent
translation cancel from the final L1 norm.
-/

open MeasureTheory MeasureTheory.Measure

namespace LpSelfSimilar.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The spatially rescaled kernel with its exact inverse-scale normalization. -/
noncomputable def rescaledKernel (r : ℝ) (f : ℝ → E) (x : ℝ) : E := r⁻¹ • f (x / r)

/-- An affine measure map transfers to the actual convolution integral. -/
theorem measureFunctionConvolution_map_affine_rescaled
    (μ : Measure ℝ) {f : ℝ → E} (hc : Continuous f) (c : ℝ) {r : ℝ} (hr : r ≠ 0) (x : ℝ) :
    measureFunctionConvolution (μ.map (fun y ↦ r * y + c)) (rescaledKernel r f) x =
      r⁻¹ • measureFunctionConvolution μ f ((x - c) / r) := by
  unfold measureFunctionConvolution rescaledKernel
  rw [integral_map (by fun_prop) (by fun_prop), integral_smul]
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro y
  congr 1
  field_simp
  ring

/-- Translation and positive rescaling of the measure preserve the rescaled convolution L1 norm. -/
theorem integral_norm_measureFunctionConvolution_map_affine_rescaled
    (μ : Measure ℝ) {f : ℝ → E} (hc : Continuous f) (c : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x, ‖measureFunctionConvolution (μ.map (fun y ↦ r * y + c)) (rescaledKernel r f) x‖) =
      ∫ x, ‖measureFunctionConvolution μ f x‖ := by
  simp_rw [measureFunctionConvolution_map_affine_rescaled μ hc c hr.ne', norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun x ↦ ‖measureFunctionConvolution μ f (x / r)‖) c,
    integral_comp_div (fun x ↦ ‖measureFunctionConvolution μ f x‖) r,
    abs_of_pos hr, smul_eq_mul]
  field_simp

end LpSelfSimilar.Analysis
