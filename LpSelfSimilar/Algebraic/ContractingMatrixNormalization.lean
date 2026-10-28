module

public import LpSelfSimilar.Algebraic.ContractingConjugateMatrix
public import LpSelfSimilar.Algebraic.StableMatrixNormalization
public import LpSelfSimilar.Geometry.RealSpectralObservations
public import LpSelfSimilar.Analysis.RankOneCovariance

@[expose] public section

/-!
# Normalized units from the actual contracting conjugates

The canonical root matrix has proved stability and separating observations.
Applying the convergent Gram construction supplies an actual normalized matrix
unit with the canonical polynomial relation and exact inverse-Mahler determinant.
For a contracting algebraic unit its defect direction is nonzero. This completes
the matrix-existence input; the actual Gaussian scalar-information reduction is
proved separately and is not assumed here.
-/

open Matrix Polynomial
open scoped Classical InnerProductSpace MatrixOrder
open LpSelfSimilar.Geometry LpSelfSimilar.Analysis

namespace LpSelfSimilar.Algebraic

/-- The canonical real root coordinates have no repetitions. -/
theorem realContractingRoot_re_injective (x : ℝ) :
    Function.Injective (fun z : realContractingRoots x => z.val.re) := by
  intro z w h
  change z.val.re = w.val.re at h
  apply Subtype.ext
  rw [← realContractingRoot_ofReal_re x z, ← realContractingRoot_ofReal_re x w, h]

/-- The explicit observation vector separates the actual canonical root representation. -/
theorem contractingConjugateMatrix_observations_separate (x : ℝ)
    (y : EuclideanSpace ℝ (ContractingRootCoordinates x))
    (h : ∀ n : ℕ, ⟪(Matrix.toEuclideanCLM (𝕜 := ℝ) (contractingConjugateMatrix x) ^ n) y,
      realSpectralObservation⟫_ℝ = 0) : y = 0 := by
  exact realSpectralObservation_separates _ _ (realContractingRoot_re_injective x)
    Subtype.val_injective (fun z => (mem_upperContractingRoots.mp z.property).2) y h

/-- Canonical algebraic data construct the normalized unit with no geometric input hypotheses. -/
theorem exists_normalized_contracting_conjugate_unit {x : ℝ} (hx : IsAlgebraicUnit x) :
    ∃ U : (Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ)ˣ,
    ∃ w : ContractingRootCoordinates x → ℝ,
      (↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ) * (↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ)ᵀ = 1 - vecMulVec w w ∧
      (↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ) * (↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ)ᴴ ≤ 1 ∧
      |(↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ).det| = (mahlerMeasure x)⁻¹ ∧
      aeval (↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ) (integerMinimalPolynomial x) = 0 := by
  have ha : IsAlgebraic ℚ x := (hx.2.1.tower_top (A := ℚ)).isAlgebraic
  obtain ⟨A, hA⟩ := contractingConjugateMatrix_isUnit ha hx.1
  have hdecay : HasGeometricPowerBound (Matrix.toEuclideanCLM (𝕜 := ℝ) (↑A : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ)) := by
    rw [hA]
    exact contractingConjugateMatrix_geometricPowerBound x
  have hsep : ∀ y : EuclideanSpace ℝ (ContractingRootCoordinates x),
      (∀ n : ℕ, ⟪(Matrix.toEuclideanCLM (𝕜 := ℝ) (↑A : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ) ^ n) y,
        realSpectralObservation⟫_ℝ = 0) → y = 0 := by
    rw [hA]
    exact contractingConjugateMatrix_observations_separate x
  obtain ⟨U, w, hcov, hle, hdet, hpoly⟩ :=
    exists_normalized_unit_of_stable_observations A realSpectralObservation hdecay hsep
  refine ⟨U, w, hcov, hle, ?_, ?_⟩
  · rw [hdet, hA]
    exact contractingConjugateMatrix_abs_det hx
  · apply hpoly
    rw [hA]
    exact contractingConjugateMatrix_aeval x

/-- The contracting parameter forces a nonzero direction and the exact covariance factor M^-2. -/
theorem exists_normalized_contracting_unit_with_direction {x : ℝ}
    (hx : IsAlgebraicUnit x) (hx0 : 0 < x) (hx1 : x < 1) :
    ∃ U : (Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ)ˣ,
    ∃ w : ContractingRootCoordinates x → ℝ,
      (↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ) * (↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ)ᵀ = 1 - vecMulVec w w ∧
      (↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ) * (↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ)ᴴ ≤ 1 ∧
      aeval (↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ) (integerMinimalPolynomial x) = 0 ∧
      w ≠ 0 ∧ 1 - w ⬝ᵥ w = (mahlerMeasure x)⁻¹ ^ 2 := by
  obtain ⟨U, w, hcov, hle, hdet, hpoly⟩ := exists_normalized_contracting_conjugate_unit hx
  have ha : IsAlgebraic ℚ x := (hx.2.1.tower_top (A := ℚ)).isAlgebraic
  have hM := one_lt_mahlerMeasure ha hx0 hx1
  have hdet1 : |(↑U : Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ).det| < 1 := by
    rw [hdet]
    exact (inv_lt_one₀ (zero_lt_one.trans hM)).mpr hM
  refine ⟨U, w, hcov, hle, hpoly, rankOneCovariance_direction_ne_zero hcov hdet1, ?_⟩
  rw [← rankOneCovariance_det_sq hcov, ← hdet, sq_abs]

end LpSelfSimilar.Algebraic
