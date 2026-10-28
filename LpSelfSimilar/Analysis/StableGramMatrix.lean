module

public import LpSelfSimilar.Analysis.StableOrbitBilinear
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# The stable orbit Gram matrix in an arbitrary finite basis

The matrix is the matrix of the proved bilinear series, so its entries,
positivity and rank-one displacement identity are consequences of that series.
The basis is arbitrary; no orthogonality is required at this stage.
-/

open Matrix
open scoped InnerProductSpace

namespace LpSelfSimilar.Analysis

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] [DecidableEq ι]

noncomputable def stableGramMatrix (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E)
    (hA : HasGeometricPowerBound A) (v : E) : Matrix ι ι ℝ :=
  (stableOrbitBilin A hA v).toMatrix b

@[simp] theorem stableGramMatrix_apply (b : Module.Basis ι ℝ E) (A : E →L[ℝ] E)
    (hA : HasGeometricPowerBound A) (v : E) (i j : ι) :
    stableGramMatrix b A hA v i j = stableOrbitGram A v (b i) (b j) := by
  simp only [stableGramMatrix, LinearMap.BilinForm.toMatrix_apply, stableOrbitBilin_apply]

/-- Observability makes the actual matrix positive definite. -/
theorem stableGramMatrix_posDef (b : Module.Basis ι ℝ E) {A : E →L[ℝ] E}
    (hA : HasGeometricPowerBound A) (v : E)
    (hsep : ∀ x : E, (∀ n : ℕ, ⟪(A ^ n) x, v⟫_ℝ = 0) → x = 0) :
    (stableGramMatrix b A hA v).PosDef := by
  exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix b
    (stableOrbitBilin A hA v) (stableOrbitBilin_isSymm A hA v)).mp
      (stableOrbitBilin_posDef hA v hsep)

/-- The exact rank-one identity in coordinates follows from the justified series shift. -/
theorem stableGramMatrix_displacement (b : Module.Basis ι ℝ E) {A : E →L[ℝ] E}
    (hA : HasGeometricPowerBound A) (v : E) :
    (LinearMap.toMatrix b b A.toLinearMap)ᵀ * stableGramMatrix b A hA v *
      LinearMap.toMatrix b b A.toLinearMap = stableGramMatrix b A hA v -
        vecMulVec (fun i => ⟪b i, v⟫_ℝ) (fun i => ⟪b i, v⟫_ℝ) := by
  unfold stableGramMatrix
  rw [← LinearMap.BilinForm.toMatrix_comp]
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Matrix.sub_apply, vecMulVec_apply,
    LinearMap.BilinForm.comp_apply, stableOrbitBilin_apply]
  exact stableOrbitGram_apply_apply hA v (b i) (b j)

end LpSelfSimilar.Analysis
