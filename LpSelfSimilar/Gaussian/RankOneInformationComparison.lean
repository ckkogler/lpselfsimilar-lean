module

public import LpSelfSimilar.Gaussian.BinaryAxisInformation
public import LpSelfSimilar.Geometry.RankOneAxis

@[expose] public section

/-!
# Exact scalar information comparison for a rank-one covariance defect

Normalize the nonzero defect direction and use the actual independent Gaussian
decomposition on that axis. If the remaining axis variance is M to the power
minus two, the binary matrix-information difference is exactly I(u*M)-I(u).
This geometric statement requires neither a chosen eigenbasis nor invertibility
of a residual covariance matrix.
-/

open MeasureTheory ProbabilityTheory Matrix
open LpSelfSimilar.Geometry LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Gaussian

/-- One actual unit axis realizes the scalar information identity at every amplitude. -/
theorem exists_axis_information_difference {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (w : ι → ℝ) (hw : w ≠ 0)
    (hA : A * Aᵀ = 1 - vecMulVec w w) {M : ℝ} (hM : M ≠ 0)
    (hvariance : 1 - w ⬝ᵥ w = M⁻¹ ^ 2) :
    ∃ e : EuclideanSpace ℝ ι, ‖e‖ = 1 ∧ ∀ u : ℝ,
      matrixInformation (PMF.uniformOfFintype Bool) (fun b => sign b • (u • e)) A -
        matrixInformation (PMF.uniformOfFintype Bool) (fun b => sign b • (u • e)) 1 =
        binaryGaussianInformation (u * M) - binaryGaussianInformation u := by
  obtain ⟨e, he, hcov⟩ := exists_unit_axis_of_rankOneCovariance w hw M⁻¹ hvariance
  have hstar : Aᴴ = Aᵀ := by ext i j; simp
  have hcov' : A * Aᴴ =
      1 + (M⁻¹ ^ 2 - 1) • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) := by
    rw [hstar, hA, hcov]
  refine ⟨e, he, fun u => ?_⟩
  simpa only [div_inv_eq_mul] using
    binary_matrixInformation_axis_difference e he (inv_ne_zero hM) A hcov' u

end LpSelfSimilar.Gaussian
