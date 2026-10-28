module

public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

/-!
# Finite power moments separate coefficients at distinct points

The transposed Vandermonde matrix is invertible for distinct nodes. Reindexing
its existing finite-dimensional theorem gives a form valid for every finite
index type, including the empty type. Only the first cardinality-many moments
are needed; the all-natural-moments formulation is convenient for orbit observations.
-/

namespace LpSelfSimilar.Algebraic

/-- The initial power moments uniquely determine coefficients at distinct nodes. -/
theorem finite_power_moments_separate {ι K : Type*} [Fintype ι] [CommRing K] [IsDomain K]
    (z : ι → K) (hz : Function.Injective z) (x : ι → K)
    (h : ∀ n : ℕ, n < Fintype.card ι → ∑ i, x i * z i ^ n = 0) : x = 0 := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have he : (fun j => x (e j)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (hz.comp e.injective)
    intro n
    simp only [Function.comp_apply]
    rw [e.sum_comp (fun i => x i * z i ^ (n : ℕ))]
    exact h n n.isLt
  ext i
  have hi := congrFun he (e.symm i)
  simpa only [e.apply_symm_apply, Pi.zero_apply] using hi

/-- Vanishing observations at every natural time force the coefficient vector to vanish. -/
theorem finite_power_moments_separate_all {ι K : Type*} [Fintype ι] [CommRing K] [IsDomain K]
    (z : ι → K) (hz : Function.Injective z) (x : ι → K)
    (h : ∀ n : ℕ, ∑ i, x i * z i ^ n = 0) : x = 0 :=
  finite_power_moments_separate z hz x (fun n _ => h n)

end LpSelfSimilar.Algebraic
