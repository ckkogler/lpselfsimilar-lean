module

public import LpSelfSimilar.Gaussian.MatrixInformation
public import LpSelfSimilar.Geometry.MatrixEquivalence
public import LpSelfSimilar.Entropy.AdditiveInformationEquiv
public import LpSelfSimilar.Probability.UniformReindex

@[expose] public section

/-!
Invertible matrix scaling and finite-input reindexing of Gaussian information.

The matrix and Gaussian are pushed forward together, using the actual unit
inverse and exact Gaussian map law. Reindexing uniform words uses the proved
PMF pushforward identity. These are used to place each retained digit at the
same pair of matrix noise scales in the finite entropy telescope.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Matrix

namespace LpSelfSimilar.Gaussian

theorem matrixInformation_reindex {Ω Ξ ι : Type*} [Fintype Ω] [Fintype Ξ]
    [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (p : PMF Ω) (X : Ξ → EuclideanSpace ℝ ι) (f : Ω → Ξ) (A : Matrix ι ι ℝ) :
    matrixInformation p (fun ω ↦ X (f ω)) A = matrixInformation (p.map f) X A := by
  let K := (additiveNoiseKernel (linearGaussian A)).comap X (measurable_of_countable X)
  have hK : (additiveNoiseKernel (linearGaussian A)).comap (fun ω ↦ X (f ω))
      (measurable_of_countable _) = K.comap f (measurable_of_countable f) := by
    ext ω : 1
    rfl
  unfold matrixInformation Entropy.additiveInformation
  rw [hK, Entropy.finiteInformation_comap_map]

lemma matrixInformation_uniform_reindex {Ω Ξ ι : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype Ξ] [Nonempty Ξ] [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (e : Ω ≃ Ξ) (X : Ξ → EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) :
    matrixInformation (PMF.uniformOfFintype Ω) (fun ω ↦ X (e ω)) A =
      matrixInformation (PMF.uniformOfFintype Ξ) X A := by
  rw [matrixInformation_reindex, uniformPMF_map_equiv]

/-- Simultaneously scaling the signal and matrix noise by a matrix unit
preserves Gaussian information exactly. -/
theorem matrixInformation_mul_left_unit {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (X : Ω → EuclideanSpace ℝ ι)
    (U : (Matrix ι ι ℝ)ˣ) (A : Matrix ι ι ℝ) :
    matrixInformation p (fun ω ↦ Matrix.toEuclideanCLM (𝕜 := ℝ) (↑U : Matrix ι ι ℝ) (X ω))
      ((↑U : Matrix ι ι ℝ) * A) = matrixInformation p X A := by
  unfold matrixInformation
  rw [← linearGaussian_map_matrix]
  exact Entropy.additiveInformation_map_equiv p X (linearGaussian A)
    (matrixUnitMeasurableEquiv U) (fun x y ↦ (Matrix.toEuclideanCLM (𝕜 := ℝ) _).map_add x y)

end LpSelfSimilar.Gaussian
