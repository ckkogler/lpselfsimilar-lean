module

public import LpSelfSimilar.Fourier.FiniteLawTransform
public import LpSelfSimilar.Fourier.ConditionalCancellation
public import LpSelfSimilar.Probability.SupportedJointLaws

@[expose] public section

/-!
# Conditional Fourier expectations are expectations of actual probability laws

Positive columns have exactly the normalized-vector transform. At null columns,
the fallback probability law is immaterial because its original label mass is
zero. Thus the finite cancellation expressions equal Bochner expectations of
Mathlib characteristic-function norms under the actual label PMF.
-/

open MeasureTheory
open scoped BigOperators
open LpSelfSimilar.Entropy LpSelfSimilar.FiniteProbability

namespace LpSelfSimilar.Fourier

/-- At every positive label, the actual conditional characteristic function is the finite transform. -/
theorem charFun_jointConditionalLaw_of_pos {ι κ : Type*} [Fintype ι]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (z : ι → ℝ)
    (j : κ) (hj : 0 < jointLabelWeight u j) (s : ℝ) :
    charFun (jointConditionalLaw u hu z j) s =
      finiteTransform (jointConditionalWeight u j) z s := by
  classical
  rw [jointConditionalLaw, dif_pos hj]
  exact charFun_realVectorLaw _ z _ _ s

/-- Averaging characteristic-function norms uses the original weights, including all null labels. -/
theorem sum_weighted_norm_charFun_jointConditionalLaw {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (z : ι → ℝ) (s : ℝ) :
    (∑ j, jointLabelWeight u j * ‖charFun (jointConditionalLaw u hu z j) s‖) =
      jointExpectedTransformNorm u z s := by
  unfold jointExpectedTransformNorm
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hq : jointLabelWeight u j = 0
  · simp [hq]
  have hqpos : 0 < jointLabelWeight u j :=
    lt_of_le_of_ne (jointLabelWeight_nonneg u hu j) (by intro h; exact hq h.symm)
  rw [charFun_jointConditionalLaw_of_pos u hu z j hqpos s]

/-- The finite expected transform norm equals the actual Bochner expectation under the label PMF. -/
theorem jointExpectedTransformNorm_eq_integral {ι κ : Type*}
    [Fintype ι] [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (hpsum : ∑ i, p i = 1)
    (z : ι → ℝ) (s : ℝ) :
    jointExpectedTransformNorm u z s =
      ∫ j, ‖charFun (jointConditionalLaw u hu.1 z j) s‖
        ∂(realVectorPMF (jointLabelWeight u) (jointLabelWeight_nonneg u hu.1)
          (sum_jointLabelWeight_eq_one p cover hu hpsum)).toMeasure := by
  rw [PMF.integral_eq_sum]
  simp only [realVectorPMF_toReal, smul_eq_mul]
  exact (sum_weighted_norm_charFun_jointConditionalLaw u hu.1 z s).symm

end LpSelfSimilar.Fourier
