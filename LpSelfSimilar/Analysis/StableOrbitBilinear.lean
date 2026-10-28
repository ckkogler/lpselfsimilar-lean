module

public import LpSelfSimilar.Analysis.StableOrbitGram
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

@[expose] public section

/-!
# The stable orbit series as a positive bilinear form

Absolute summability justifies linearity of the Gram series. Its symmetric
bilinear form has a positive definite quadratic form whenever the orbit
observations separate vectors. No new positivity assumption is built into
the definition; positivity is proved from that separation condition.
-/

open scoped InnerProductSpace

namespace LpSelfSimilar.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem stableOrbitGram_add_left {A : E →L[ℝ] E} (hA : HasGeometricPowerBound A)
    (v x y z : E) :
    stableOrbitGram A v (x + y) z = stableOrbitGram A v x z + stableOrbitGram A v y z := by
  unfold stableOrbitGram
  simp_rw [map_add, inner_add_left, add_mul]
  exact (summable_stableOrbitGram hA v x z).tsum_add (summable_stableOrbitGram hA v y z)

theorem stableOrbitGram_smul_left (A : E →L[ℝ] E) (v x y : E) (c : ℝ) :
    stableOrbitGram A v (c • x) y = c * stableOrbitGram A v x y := by
  unfold stableOrbitGram
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [map_smul, real_inner_smul_left, mul_assoc]

theorem stableOrbitGram_add_right {A : E →L[ℝ] E} (hA : HasGeometricPowerBound A)
    (v x y z : E) :
    stableOrbitGram A v x (y + z) = stableOrbitGram A v x y + stableOrbitGram A v x z := by
  rw [stableOrbitGram_symm A v x, stableOrbitGram_add_left hA]
  rw [stableOrbitGram_symm A v y x, stableOrbitGram_symm A v z x]

theorem stableOrbitGram_smul_right (A : E →L[ℝ] E) (v x y : E) (c : ℝ) :
    stableOrbitGram A v x (c • y) = c * stableOrbitGram A v x y := by
  rw [stableOrbitGram_symm A v x, stableOrbitGram_smul_left, stableOrbitGram_symm A v y x]

/-- The actual series packaged as a bilinear form; the decay proof justifies its addition laws. -/
noncomputable def stableOrbitBilin (A : E →L[ℝ] E) (hA : HasGeometricPowerBound A) (v : E) :
    LinearMap.BilinForm ℝ E where
  toFun x :=
    { toFun := stableOrbitGram A v x
      map_add' := stableOrbitGram_add_right hA v x
      map_smul' := by
        intro c y
        simpa only [RingHom.id_apply, smul_eq_mul] using stableOrbitGram_smul_right A v x y c }
  map_add' x y := by
    ext z
    exact stableOrbitGram_add_left hA v x y z
  map_smul' c x := by
    ext y
    change stableOrbitGram A v (c • x) y = c * stableOrbitGram A v x y
    exact stableOrbitGram_smul_left A v x y c

@[simp] theorem stableOrbitBilin_apply (A : E →L[ℝ] E) (hA : HasGeometricPowerBound A)
    (v x y : E) : stableOrbitBilin A hA v x y = stableOrbitGram A v x y := rfl

theorem stableOrbitBilin_isSymm (A : E →L[ℝ] E) (hA : HasGeometricPowerBound A) (v : E) :
    (stableOrbitBilin A hA v).IsSymm :=
  ⟨stableOrbitGram_symm A v⟩

/-- Observability proves strict positivity of the quadratic form. -/
theorem stableOrbitBilin_posDef {A : E →L[ℝ] E} (hA : HasGeometricPowerBound A) (v : E)
    (hsep : ∀ x : E, (∀ n : ℕ, ⟪(A ^ n) x, v⟫_ℝ = 0) → x = 0) :
    (stableOrbitBilin A hA v).toQuadraticMap.PosDef := by
  intro x hx
  exact stableOrbitGram_pos hA v hsep hx

end LpSelfSimilar.Analysis
