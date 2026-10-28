module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Probability.Centering
public import Mathlib.MeasureTheory.Group.Convolution

@[expose] public section

/-!
# Affine normalization of finite convolution factors

Scaling commutes with finite convolution, and translating the factors translates
their convolution by the sum of the translations. Thus the individually
normalized conditional laws give the actual normalization of the original sum.
-/

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace LpSelfSimilar

/-- Scaling all finite convolution factors scales their actual sum law. -/
theorem finiteConvolution_map_mul {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (r : ℝ) :
    finiteConvolution (fun i ↦ (μ i).map (fun y ↦ r * y)) =
      (finiteConvolution μ).map (fun y ↦ r * y) := by
  haveI (i : Fin n) : IsProbabilityMeasure ((μ i).map (fun y ↦ r * y)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  induction n with
  | zero => simp [finiteConvolution]
  | succ n ih =>
    rw [finiteConvolution, ih (fun i ↦ μ i.succ) (fun i ↦ inferInstance), finiteConvolution]
    simpa [Pi.smul_def, smul_eq_mul] using (map_conv_continuousLinearMap (μ := μ 0)
      (ν := finiteConvolution (fun i : Fin n ↦ μ i.succ)) (r • ContinuousLinearMap.id ℝ ℝ)).symm

/-- Normalizing each conditional factor is the same as normalizing its actual sum. -/
theorem finiteConvolution_map_sub_div {n : ℕ} (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (c : Fin n → ℝ) (r : ℝ) :
    finiteConvolution (fun i ↦ (μ i).map (fun y ↦ (y - c i) / r)) =
      (finiteConvolution μ).map (fun y ↦ (y - ∑ i, c i) / r) := by
  haveI (i : Fin n) : IsProbabilityMeasure ((μ i).map (fun y ↦ y + -c i)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  have he i : (μ i).map (fun y ↦ (y - c i) / r) =
      ((μ i).map (fun y ↦ y + -c i)).map (fun y ↦ (1 / r) * y) := by
    rw [map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext y
    dsimp only [Function.comp_apply]
    ring
  simp_rw [he]
  rw [finiteConvolution_map_mul, finiteConvolution_translate,
    map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext y
  simp only [Function.comp_apply, Finset.sum_neg_distrib]
  ring

/-- The normalized law recovers the original measure by the actual inverse affine map. -/
theorem map_sub_div_inverse (μ : Measure ℝ) (c : ℝ) {r : ℝ} (hr : r ≠ 0) :
    (μ.map (fun y ↦ (y - c) / r)).map (fun y ↦ r * y + c) = μ := by
  rw [map_map (by fun_prop) (by fun_prop)]
  have he : (fun y : ℝ ↦ r * ((y - c) / r) + c) = id := by
    funext y
    dsimp only [id_eq]
    field_simp
    ring
  change μ.map (fun y ↦ r * ((y - c) / r) + c) = μ
  rw [he, map_id]

/-- Affine normalization is translation followed by linear scaling. -/
theorem map_sub_div_eq_map_mul_map_add (μ : Measure ℝ) (c r : ℝ) :
    μ.map (fun y ↦ (y - c) / r) =
      (μ.map (fun y ↦ y + -c)).map (fun y ↦ (1 / r) * y) := by
  rw [map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext y
  dsimp only [Function.comp_apply]
  ring

/-- Normalizing a block and its independent tail normalizes their actual sum. -/
theorem conv_map_sub_div_map_div (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c r : ℝ) :
    (μ.map (fun y ↦ (y - c) / r)) ∗ (ν.map (fun y ↦ y / r)) =
      (μ ∗ ν).map (fun y ↦ (y - c) / r) := by
  haveI : IsProbabilityMeasure (μ.map (fun y ↦ y + -c)) :=
    LpSelfSimilar.Probability.isProbabilityMeasure_map (by fun_prop)
  have hscale (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
      (α.map (fun y ↦ (1 / r) * y)) ∗ (β.map (fun y ↦ (1 / r) * y)) =
        (α ∗ β).map (fun y ↦ (1 / r) * y) := by
    simpa [Pi.smul_def, smul_eq_mul] using
      (map_conv_continuousLinearMap (μ := α) (ν := β)
        ((1 / r) • ContinuousLinearMap.id ℝ ℝ)).symm
  have ht : (μ.map (fun y ↦ y + -c)) ∗ ν = (μ ∗ ν).map (fun y ↦ y + -c) := by
    rw [← conv_dirac, ← conv_dirac, conv_assoc, conv_comm (dirac (-c)) ν, ← conv_assoc]
  have he : (fun y : ℝ ↦ y / r) = fun y ↦ (1 / r) * y := by funext y; ring
  rw [map_sub_div_eq_map_mul_map_add, he, hscale, ht,
    ← map_sub_div_eq_map_mul_map_add]

end LpSelfSimilar
