module

public import LpSelfSimilar.Algebraic.ContractingRootPairs
public import LpSelfSimilar.Geometry.RealSpectralContraction

@[expose] public section

/-!
# The canonical real contracting-conjugate matrix

Each real contracting root supplies one real coordinate. Each nonreal pair
supplies the two real coordinates of its upper-half-plane representative.
The actual block matrix is annihilated by the canonical integer minimal
polynomial, is invertible for a nonzero algebraic parameter, is geometrically
stable, and has determinant modulus equal to the inverse Mahler measure for
an algebraic unit. Its separating observation vector is established separately.
-/

open Matrix Polynomial
open scoped Classical
open LpSelfSimilar.Geometry

namespace LpSelfSimilar.Algebraic

/-- One real coordinate per real root and two per nonreal conjugate pair. -/
abbrev ContractingRootCoordinates (x : ℝ) :=
  ↥(realContractingRoots x) ⊕ (Fin 2 × ↥(upperContractingRoots x))

/-- The real multiplication matrix of the actual canonical contracting roots. -/
noncomputable def contractingConjugateMatrix (x : ℝ) :
    Matrix (ContractingRootCoordinates x) (ContractingRootCoordinates x) ℝ := by
  classical
  exact realSpectralMatrix (fun z : realContractingRoots x => z.val.re)
    (fun z : upperContractingRoots x => z.val)

theorem contractingConjugateMatrix_isUnit {x : ℝ} (hx : IsAlgebraic ℚ x) (hx0 : x ≠ 0) :
    IsUnit (contractingConjugateMatrix x) := by
  classical
  exact realSpectralMatrix_isUnit _ _ (realContractingRoot_re_ne_zero hx hx0)
    (fun z => upperContractingRoot_ne_zero z)

theorem contractingConjugateMatrix_abs_det {x : ℝ} (hx : IsAlgebraicUnit x) :
    |(contractingConjugateMatrix x).det| = (mahlerMeasure x)⁻¹ := by
  classical
  rw [contractingConjugateMatrix, realSpectralMatrix_det, abs_mul, Finset.abs_prod,
    abs_of_nonneg (Finset.prod_nonneg (fun _ _ => sq_nonneg _))]
  exact prod_real_upper_contracting_norms hx

theorem realContractingRoot_aeval (x : ℝ) (z : realContractingRoots x) :
    aeval z.val.re (integerMinimalPolynomial x) = 0 := by
  have he := (mem_aroots.mp
    (mem_contractingConjugates.mp (mem_realContractingRoots.mp z.property).1).1).2
  rw [← realContractingRoot_ofReal_re x z] at he
  change aeval (algebraMap ℝ ℂ z.val.re) (integerMinimalPolynomial x) = 0 at he
  rw [aeval_algebraMap_apply] at he
  exact (algebraMap ℝ ℂ).injective (by simpa only [map_zero] using he)

theorem upperContractingRoot_aeval (x : ℝ) (z : upperContractingRoots x) :
    aeval z.val (integerMinimalPolynomial x) = 0 :=
  (mem_aroots.mp
    (mem_contractingConjugates.mp (mem_upperContractingRoots.mp z.property).1).1).2

/-- No extra polynomial relation is assumed: every actual root supplies its block relation. -/
theorem contractingConjugateMatrix_aeval (x : ℝ) :
    aeval (contractingConjugateMatrix x) (integerMinimalPolynomial x) = 0 := by
  classical
  rw [contractingConjugateMatrix, aeval_realSpectralMatrix]
  simp only [realContractingRoot_aeval, upperContractingRoot_aeval, realSpectralMatrix_zero]

/-- The actual root moduli prove the geometric decay required by Gram normalization. -/
theorem contractingConjugateMatrix_geometricPowerBound (x : ℝ) :
    Analysis.HasGeometricPowerBound
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (contractingConjugateMatrix x)) := by
  classical
  apply realSpectralMatrix_geometricPowerBound
  · intro z
    rw [← realContractingRoot_norm x z]
    exact (mem_contractingConjugates.mp (mem_realContractingRoots.mp z.property).1).2
  · intro z
    exact (mem_contractingConjugates.mp (mem_upperContractingRoots.mp z.property).1).2

end LpSelfSimilar.Algebraic
