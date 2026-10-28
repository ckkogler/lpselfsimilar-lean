module

public import LpSelfSimilar.Probability.MapProbability

public import LpSelfSimilar.Geometry.RealLine
public import LpSelfSimilar.Bernoulli.Decomposition
public import LpSelfSimilar.SelfSimilar.Definitions

@[expose] public section

/-!
The actual Bernoulli convolution as a stationary measure of two contracting
Euclidean similarities. Conjugacy is through a volume-preserving isometry,
so the existing Euclidean self-similar theorems apply without a normalization
factor or an additional geometric assumption.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace LpSelfSimilar.Bernoulli

noncomputable def euclideanLaw (l : ℝ) : Measure (Space 1) :=
  (convolution l).map realLine.symm

instance euclideanLaw_probability (l : ℝ) : IsProbabilityMeasure (euclideanLaw l) :=
  LpSelfSimilar.Probability.isProbabilityMeasure_map realLine.symm.continuous.measurable.aemeasurable

noncomputable def digitSimilarity {l : ℝ} (hl : 0 < l) (e : Bool) : Similarity 1 where
  ratio := l
  ratio_pos := hl
  orthogonal := LinearIsometryEquiv.refl ℝ (Space 1)
  shift := realLine.symm (sign e)

lemma digitSimilarity_conjugate {l : ℝ} (hl : 0 < l) (e : Bool) (x : ℝ) :
    digitSimilarity hl e (realLine.symm x) = realLine.symm (l * x + sign e) := by
  simp [digitSimilarity, ← smul_eq_mul]

noncomputable def selfSimilarSystem {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    SelfSimilar.System 1 Bool where
  map := digitSimilarity hl
  contracting := fun _ ↦ hl1
  weight := fun _ ↦ 1 / 2
  weight_sum := by norm_num [Fintype.sum_bool]

lemma convolution_stationary_sum {l : ℝ} (hl : |l| < 1) :
    convolution l = ∑ e : Bool, (1 / 2 : ℝ≥0∞) •
      (convolution l).map (fun x ↦ l * x + sign e) := by
  simpa [Fintype.sum_bool, sign, sub_eq_add_neg] using convolution_stationary hl

/-- Exact stationarity of the transported measure for the two Euclidean maps. -/
theorem euclideanLaw_stationary {l : ℝ} (hl : 0 < l) (hl1 : l < 1) :
    (selfSimilarSystem hl hl1).IsStationary (euclideanLaw l) := by
  have habs : |l| < 1 := by rwa [abs_of_pos hl]
  change (convolution l).map realLine.symm =
    ∑ e : Bool, ((1 / 2 : ℝ≥0) : ℝ≥0∞) •
      ((convolution l).map realLine.symm).map (digitSimilarity hl e)
  have hc : ((1 / 2 : ℝ≥0) : ℝ≥0∞) = (1 / 2 : ℝ≥0∞) := by norm_num
  simp_rw [hc]
  conv_lhs => rw [convolution_stationary_sum habs]
  rw [Measure.map_finset_sum (by fun_prop)]
  simp_rw [Measure.map_smul]
  apply Finset.sum_congr rfl
  intro e _
  congr 1
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (digitSimilarity hl e).measurable (by fun_prop)]
  congr 1

lemma realLine_map_euclideanLaw (l : ℝ) : (euclideanLaw l).map realLine = convolution l := by
  rw [euclideanLaw, Measure.map_map realLine.continuous.measurable
    realLine.symm.continuous.measurable]
  simp

end LpSelfSimilar.Bernoulli
