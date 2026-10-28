module

public import LpSelfSimilar.Fourier.FinitePhaseCancellation
public import LpSelfSimilar.Entropy.SupportedJointCancellation

@[expose] public section

/-!
# One Fourier shift for all conditional labels

The joint array determines the original label probabilities and normalized
conditional vectors. Averaging their Fourier norms does not discard null labels
or change label weights. Averaging first over a finite shift distribution lets us
choose one common shift before the conditional label is sampled.
-/

open scoped BigOperators
open LpSelfSimilar.Entropy

namespace LpSelfSimilar.Fourier

/-- Expected norm of the actual conditional finite transforms under the original label masses. -/
noncomputable def jointExpectedTransformNorm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → κ → ℝ) (z : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ j, jointLabelWeight u j * ‖finiteTransform (jointConditionalWeight u j) z s‖

/-- Conditional expected Fourier norms are nonnegative. -/
theorem jointExpectedTransformNorm_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → κ → ℝ) (hu : ∀ i j, 0 ≤ u i j) (z : ι → ℝ) (s : ℝ) :
    0 ≤ jointExpectedTransformNorm u z s :=
  Finset.sum_nonneg fun j _ ↦
    mul_nonneg (jointLabelWeight_nonneg u hu j) (norm_nonneg _)

/-- Finite shift averaging commutes with averaging over the original conditional labels. -/
theorem weighted_jointExpectedTransformNorm_eq {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (u : ι → κ → ℝ) (z : ι → ℝ) (w s : τ → ℝ) :
    (∑ k, w k * jointExpectedTransformNorm u z (s k)) =
      ∑ j, jointLabelWeight u j *
        ∑ k, w k * ‖finiteTransform (jointConditionalWeight u j) z (s k)‖ := by
  simp only [jointExpectedTransformNorm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The finite phase estimate survives expectation over all conditional laws. -/
theorem weighted_jointExpectedTransformNorm_le {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (hpsum : ∑ i, p i = 1)
    (z : ι → ℝ) (w s : τ → ℝ) (hw : ∀ k, 0 ≤ w k) (hwsum : ∑ k, w k = 1)
    (hphase : ∀ j, 0 < jointLabelWeight u j → ∀ i l, i ≠ l →
      jointConditionalWeight u j i ≠ 0 → jointConditionalWeight u j l ≠ 0 →
      (3 / 5 : ℝ) ≤ ∑ k, w k * (1 - Real.cos (s k * (z i - z l)))) :
    (∑ k, w k * jointExpectedTransformNorm u z (s k)) ≤
      1 - jointExpectedCancellation u := by
  have hcol (j : κ) : jointLabelWeight u j *
      (∑ k, w k * ‖finiteTransform (jointConditionalWeight u j) z (s k)‖) ≤
      jointLabelWeight u j *
        (1 - finiteCancellation Finset.univ (jointConditionalWeight u j)) := by
    by_cases hq : jointLabelWeight u j = 0
    · simp [hq]
    have hqpos : 0 < jointLabelWeight u j :=
      lt_of_le_of_ne (jointLabelWeight_nonneg u hu.1 j) (by intro h; exact hq h.symm)
    apply mul_le_mul_of_nonneg_left _ hqpos.le
    exact weighted_norm_finiteTransform_le_one_sub_cancellation
      (jointConditionalWeight u j) z w s
      (jointConditionalWeight_nonneg u hu.1 j)
      (sum_jointConditionalWeight_eq_one u j hqpos) hw hwsum (hphase j hqpos)
  rw [weighted_jointExpectedTransformNorm_eq]
  calc
    _ ≤ ∑ j, jointLabelWeight u j *
        (1 - finiteCancellation Finset.univ (jointConditionalWeight u j)) :=
      Finset.sum_le_sum fun j _ ↦ hcol j
    _ = 1 - jointExpectedCancellation u := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib,
        sum_jointLabelWeight_eq_one p cover hu hpsum, jointExpectedCancellation]

/-- A single fixed shift attains the expected conditional cancellation. -/
theorem exists_common_shift_of_phase_estimate {ι κ τ : Type*}
    [Fintype ι] [Fintype κ] [Fintype τ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (hpsum : ∑ i, p i = 1)
    (z : ι → ℝ) (w s : τ → ℝ) (hw : ∀ k, 0 ≤ w k) (hwsum : ∑ k, w k = 1)
    (hphase : ∀ j, 0 < jointLabelWeight u j → ∀ i l, i ≠ l →
      jointConditionalWeight u j i ≠ 0 → jointConditionalWeight u j l ≠ 0 →
      (3 / 5 : ℝ) ≤ ∑ k, w k * (1 - Real.cos (s k * (z i - z l)))) :
    ∃ k, jointExpectedTransformNorm u z (s k) ≤ 1 - jointExpectedCancellation u :=
  Analysis.exists_le_of_weighted_sum_le w (fun k ↦ jointExpectedTransformNorm u z (s k))
    hw hwsum (weighted_jointExpectedTransformNorm_le p cover hu hpsum z w s hw hwsum hphase)

end LpSelfSimilar.Fourier
