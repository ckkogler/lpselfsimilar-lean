module

public import LpSelfSimilar.Bernoulli.EuclideanSystem
public import LpSelfSimilar.Geometry.SimilarityVolume

@[expose] public section

/-!
The known Bernoulli support interval transported to one-dimensional Euclidean
space. Its explicit diameter is retained in (2.2), which rigorously replaces
the paper's affine diameter normalization without changing the measure.
-/

open MeasureTheory Metric Set

namespace LpSelfSimilar.Bernoulli

noncomputable def euclideanSupport (l : ℝ) : Set (Space 1) :=
  realLine ⁻¹' Icc (-(1 - l)⁻¹) (1 - l)⁻¹

lemma measurableSet_euclideanSupport (l : ℝ) : MeasurableSet (euclideanSupport l) :=
  measurableSet_Icc.preimage realLine.continuous.measurable

lemma euclideanSupport_compl_null {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) :
    euclideanLaw l (euclideanSupport l)ᶜ = 0 := by
  rw [euclideanLaw, Measure.map_apply realLine.symm.continuous.measurable
    (measurableSet_euclideanSupport l).compl]
  have he : realLine.symm ⁻¹' (euclideanSupport l)ᶜ = (Icc (-(1 - l)⁻¹) (1 - l)⁻¹)ᶜ := by
    ext x
    simp [euclideanSupport]
  rw [he]
  exact convolution_compl_interval l hl hl1

lemma euclideanSupport_mass {l : ℝ} (hl : 0 ≤ l) (hl1 : l < 1) :
    euclideanLaw l (euclideanSupport l) = 1 := by
  have h := measure_add_measure_compl (μ := euclideanLaw l) (measurableSet_euclideanSupport l)
  simpa only [euclideanSupport_compl_null hl hl1, add_zero, measure_univ] using h

lemma euclideanSupport_diameter {l : ℝ} {x y : Space 1}
    (hx : x ∈ euclideanSupport l) (hy : y ∈ euclideanSupport l) :
    dist x y ≤ 2 / (1 - l) := by
  rw [← realLine.dist_map, Real.dist_eq]
  have hx' : -(1 - l)⁻¹ ≤ realLine x ∧ realLine x ≤ (1 - l)⁻¹ := hx
  have hy' : -(1 - l)⁻¹ ≤ realLine y ∧ realLine y ≤ (1 - l)⁻¹ := hy
  rw [abs_le]
  constructor <;> simp only [div_eq_mul_inv] <;> linarith

lemma bernoulli_smallSetConstant {l : ℝ} :
    smallSetConstant 1 l (2 / (1 - l)) = 4 / (l * (1 - l)) := by
  rw [smallSetConstant, pow_one, volume_realLine_unitBall]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end LpSelfSimilar.Bernoulli
