module

public import LpSelfSimilar.Geometry.RealSpectralContraction
public import LpSelfSimilar.Algebraic.RealComplexMoments

@[expose] public section

/-!
# Separating observations for the real spectral matrix

The observation vector assigns weight one to real coordinates and weight two
to the real coordinate in each complex block. Its orbit observations are the
real power moments of the distinct conjugate-paired spectral nodes. The proved
finite Vandermonde argument makes those observations separate all vectors.
-/

open Matrix
open scoped InnerProductSpace

namespace LpSelfSimilar.Geometry

variable {R C : Type*} [Fintype R] [DecidableEq R] [Fintype C] [DecidableEq C]

/-- Action of a homogeneous block diagonal matrix on a coordinate block. -/
theorem blockDiagonal_mulVec_coordinate (B : C → Matrix (Fin 2) (Fin 2) ℝ)
    (x : Fin 2 × C → ℝ) (i : Fin 2) (j : C) :
    (blockDiagonal B *ᵥ x) (i,j) = (B j *ᵥ (fun k => x (k,j))) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply]

theorem realSpectralMatrix_mulVec_real (a : R → ℝ) (z : C → ℂ)
    (x : R ⊕ (Fin 2 × C) → ℝ) (i : R) :
    (realSpectralMatrix a z *ᵥ x) (Sum.inl i) = a i * x (Sum.inl i) := by
  simp only [realSpectralMatrix, fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    Sum.elim_inl, mulVec_diagonal, Pi.mul_apply, Function.comp_apply]

theorem realSpectralMatrix_mulVec_complex_real (a : R → ℝ) (z : C → ℂ)
    (x : R ⊕ (Fin 2 × C) → ℝ) (j : C) :
    (realSpectralMatrix a z *ᵥ x) (Sum.inr (0,j)) =
      (z j * (⟨x (Sum.inr (0,j)), x (Sum.inr (1,j))⟩ : ℂ)).re := by
  simp only [realSpectralMatrix, fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, zero_add,
    Sum.elim_inr]
  rw [blockDiagonal_mulVec_coordinate, complexRealMatrix_mulVec]
  rfl

/-- The actual real vector that sums each conjugate pair's real observation. -/
noncomputable def realSpectralObservation : EuclideanSpace ℝ (R ⊕ (Fin 2 × C)) :=
  WithLp.toLp 2 (Sum.elim (fun _ => 1) (fun j => if j.1 = 0 then 2 else 0))

/-- Orbit observations are exactly the real power moments at the spectral nodes. -/
theorem realSpectralObservation_inner (a : R → ℝ) (z : C → ℂ)
    (x : EuclideanSpace ℝ (R ⊕ (Fin 2 × C))) (n : ℕ) :
    ⟪(Matrix.toEuclideanCLM (𝕜 := ℝ) (realSpectralMatrix a z) ^ n) x,
      realSpectralObservation⟫_ℝ =
      (∑ i, x (Sum.inl i) * a i ^ n) +
        2 * ∑ j, ((⟨x (Sum.inr (0,j)), x (Sum.inr (1,j))⟩ : ℂ) * z j ^ n).re := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  rw [← map_pow, realSpectralMatrix_pow, real_inner_comm, Matrix.inner_toEuclideanCLM]
  simp only [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    realSpectralObservation, Sum.elim_inl, Sum.elim_inr]
  simp only [ite_true, h10, ite_false, one_mul, zero_mul, Finset.sum_const_zero, add_zero]
  simp_rw [realSpectralMatrix_mulVec_real, realSpectralMatrix_mulVec_complex_real]
  rw [← Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm]

/-- Distinct real nodes and distinct upper-half-plane nodes give separating observations. -/
theorem realSpectralObservation_separates (a : R → ℝ) (z : C → ℂ)
    (ha : Function.Injective a) (hz : Function.Injective z) (hi : ∀ j, 0 < (z j).im)
    (x : EuclideanSpace ℝ (R ⊕ (Fin 2 × C)))
    (h : ∀ n : ℕ, ⟪(Matrix.toEuclideanCLM (𝕜 := ℝ) (realSpectralMatrix a z) ^ n) x,
      realSpectralObservation⟫_ℝ = 0) : x = 0 := by
  have hm := Algebraic.real_complex_power_moments_separate a z ha hz hi
    (fun i => x (Sum.inl i))
    (fun j => (⟨x (Sum.inr (0,j)), x (Sum.inr (1,j))⟩ : ℂ))
    (fun n => (realSpectralObservation_inner a z x n).symm.trans (h n))
  ext i
  rcases i with i | ⟨k,j⟩
  · exact congrFun hm.1 i
  · have hj := congrFun hm.2 j
    fin_cases k
    · exact congrArg Complex.re hj
    · exact congrArg Complex.im hj

end LpSelfSimilar.Geometry
