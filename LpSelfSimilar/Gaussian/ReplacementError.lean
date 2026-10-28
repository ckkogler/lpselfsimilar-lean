module

public import LpSelfSimilar.Gaussian.SingleReplacement
public import LpSelfSimilar.Gaussian.ConvolutionDetail

@[expose] public section

/-!
The L1 error of the smoothed first derivative relative to a Gaussian of matching
variance. A convolution step propagates the first replacement error by L1
contraction and moves its Gaussian variance into the remaining smoothing scale.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real
open scoped NNReal

namespace LpSelfSimilar.Gaussian

noncomputable def replacementError (μ : Measure ℝ) (v : ℝ≥0) (y : ℝ) : ℝ :=
  ∫ x, |firstSmooth μ y x - firstKernel ((v : ℝ) + y) x|

lemma replacementError_nonneg (μ : Measure ℝ) (v : ℝ≥0) (y : ℝ) :
    0 ≤ replacementError μ v y := integral_nonneg (fun _ ↦ abs_nonneg _)

lemma replacementError_dirac_zero (y : ℝ) : replacementError (dirac 0) 0 y = 0 := by
  simp [replacementError, firstSmooth, averageTranslate]

lemma replacementError_conv_le (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (v w : ℝ≥0)
    {y : ℝ} (hy : 0 < y) :
    replacementError (μ ∗ ν) (v + w) y ≤
      replacementError μ v y + replacementError ν w ((v : ℝ) + y) := by
  have hnew : 0 < (v : ℝ) + y := by positivity
  have htotal : 0 < (w : ℝ) + ((v : ℝ) + y) := by positivity
  let F (x : ℝ) := firstSmooth μ y x - firstKernel ((v : ℝ) + y) x
  let G (x : ℝ) := firstSmooth ν ((v : ℝ) + y) x - firstKernel ((w : ℝ) + ((v : ℝ) + y)) x
  have hFc : Continuous F := (continuous_firstSmooth_space μ hy).sub (continuous_firstKernel _)
  have hFi : Integrable F volume := (integrable_firstSmooth μ hy).sub (integrable_firstKernel hnew)
  have hGi : Integrable G volume := (integrable_firstSmooth ν hnew).sub (integrable_firstKernel htotal)
  have hFb (x : ℝ) : |firstSmooth μ y x| ≤ 3 / (2 * y) * (Real.sqrt (2 * Real.pi * y))⁻¹ :=
    abs_averageTranslate_le μ (abs_firstKernel_le hy) x
  have he (x : ℝ) : firstSmooth (μ ∗ ν) y x - firstKernel (((v + w : ℝ≥0) : ℝ) + y) x =
      averageTranslate ν F x + G x := by
    rw [Measure.conv_comm, firstSmooth_conv ν μ hy]
    dsimp only [F, G]
    rw [averageTranslate_sub ν (continuous_firstSmooth_space μ hy) (continuous_firstKernel _)
      hFb (abs_firstKernel_le hnew)]
    change _ - firstKernel (((v + w : ℝ≥0) : ℝ) + y) x =
      _ - firstSmooth ν ((v : ℝ) + y) x +
        (firstSmooth ν ((v : ℝ) + y) x - firstKernel ((w : ℝ) + ((v : ℝ) + y)) x)
    rw [NNReal.coe_add, show (v : ℝ) + w + y = w + ((v : ℝ) + y) by ring]
    ring
  have hconv := integral_abs_averageTranslate_le ν hFc hFi
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_mul] at hconv
  unfold replacementError
  simp_rw [he]
  calc
    (∫ x, |averageTranslate ν F x + G x|) ≤ ∫ x, |averageTranslate ν F x| + |G x| :=
      integral_mono ((integrable_averageTranslate ν hFc hFi).add hGi).abs
        ((integrable_averageTranslate ν hFc hFi).abs.add hGi.abs) (fun x ↦ abs_add_le _ _)
    _ = (∫ x, |averageTranslate ν F x|) + ∫ x, |G x| :=
      integral_add (integrable_averageTranslate ν hFc hFi).abs hGi.abs
    _ ≤ _ := add_le_add hconv le_rfl

end LpSelfSimilar.Gaussian
