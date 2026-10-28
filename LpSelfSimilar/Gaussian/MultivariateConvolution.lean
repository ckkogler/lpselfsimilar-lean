module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
Exact convolution of centered multivariate Gaussian laws.

Positive semidefinite covariance matrices are sufficient; the laws may be
singular. Characteristic functions prove that independent covariances add.
Consequently an ordered pair of covariances has an actual Gaussian residual
noise law, rather than an assumed convolution decomposition.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace LpSelfSimilar.Gaussian

/-- Independent centered Gaussian covariances add, including singular cases. -/
theorem centered_multivariateGaussian_conv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S T : Matrix ι ι ℝ} (hS : S.PosSemidef) (hT : T.PosSemidef) :
    multivariateGaussian 0 S ∗ multivariateGaussian 0 T =
      multivariateGaussian 0 (S + T) := by
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_conv, charFun_multivariateGaussian hS, charFun_multivariateGaussian hT,
    charFun_multivariateGaussian (hS.add hT), ← Complex.exp_add]
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub,
    Matrix.add_mulVec, dotProduct_add, Complex.ofReal_add]
  ring

/-- The difference of ordered covariance matrices supplies the independent
Gaussian noise completing the smaller covariance to the larger one. -/
theorem centered_multivariateGaussian_residual {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S T : Matrix ι ι ℝ} (hS : S.PosSemidef) (hST : S ≤ T) :
    multivariateGaussian 0 S ∗ multivariateGaussian 0 (T - S) =
      multivariateGaussian 0 T := by
  rw [centered_multivariateGaussian_conv hS hST, add_sub_cancel]

end LpSelfSimilar.Gaussian
