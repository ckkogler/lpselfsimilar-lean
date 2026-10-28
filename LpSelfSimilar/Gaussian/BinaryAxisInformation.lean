module

public import LpSelfSimilar.Gaussian.AxisInformation
public import LpSelfSimilar.Gaussian.BinaryChannelDensity
public import LpSelfSimilar.Bernoulli.Digits

@[expose] public section

/-!
# Binary information along a unit Gaussian axis

The finite-channel information of the actual fair-sign vector equals the
existing scalar binary Gaussian information at the amplitude divided by the
axis noise scale. Subtracting the standard-noise value retains an exact
difference, which is essential when the covariance defect is small.
-/

open MeasureTheory ProbabilityTheory Matrix
open LpSelfSimilar.Geometry LpSelfSimilar.Bernoulli

namespace LpSelfSimilar.Gaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem binary_matrixInformation_axis (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1)
    {s : ℝ} (hs : s ≠ 0) (A : Matrix ι ι ℝ)
    (hA : A * Aᴴ = 1 + (s ^ 2 - 1) • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e))
    (u : ℝ) :
    matrixInformation (PMF.uniformOfFintype Bool) (fun b => sign b • (u • e)) A =
      binaryGaussianInformation (u / s) := by
  calc
    _ = Entropy.additiveInformation (PMF.uniformOfFintype Bool)
        (fun b => sign b * u / s) (gaussianReal 0 1) := by
      simpa only [smul_smul] using
        matrixInformation_axis (PMF.uniformOfFintype Bool) (fun b => sign b * u) e he hs A hA
    _ = binaryGaussianInformation (u / s) := by
      unfold binaryGaussianInformation
      congr 1
      funext b
      cases b <;> simp [sign, neg_div]

/-- Standard ambient Gaussian information is exactly the scalar value on a unit axis. -/
theorem binary_matrixInformation_axis_one (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1)
    (u : ℝ) :
    matrixInformation (PMF.uniformOfFintype Bool) (fun b => sign b • (u • e)) 1 =
      binaryGaussianInformation u := by
  simpa only [div_one] using
    binary_matrixInformation_axis e he (s := 1) one_ne_zero 1 (by simp) u

/-- The difference at the two actual matrix noise laws is the exact scalar information gain. -/
theorem binary_matrixInformation_axis_difference (e : EuclideanSpace ℝ ι) (he : ‖e‖ = 1)
    {s : ℝ} (hs : s ≠ 0) (A : Matrix ι ι ℝ)
    (hA : A * Aᴴ = 1 + (s ^ 2 - 1) • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e))
    (u : ℝ) :
    matrixInformation (PMF.uniformOfFintype Bool) (fun b => sign b • (u • e)) A -
      matrixInformation (PMF.uniformOfFintype Bool) (fun b => sign b • (u • e)) 1 =
      binaryGaussianInformation (u / s) - binaryGaussianInformation u := by
  rw [binary_matrixInformation_axis e he hs A hA, binary_matrixInformation_axis_one e he]

end LpSelfSimilar.Gaussian
