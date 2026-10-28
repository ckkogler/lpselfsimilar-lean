module

public import LpSelfSimilar.Bernoulli.DigitCancellationBudget
public import LpSelfSimilar.Fourier.BandBlock
public import LpSelfSimilar.Fourier.ConditionalLawTransform
public import LpSelfSimilar.Probability.FiniteSupportLaw
public import LpSelfSimilar.Probability.FiniteLawSupport
public import LpSelfSimilar.Probability.FiniteLawMaps

@[expose] public section

/-!
# Actual Bernoulli digit blocks with conditional Fourier attenuation

The labels and conditional measures come from the same maximizing joint law as
the integrated digit cancellation budget. Their mixture is exactly the merged
finite Bernoulli digit law. A common integer shift gives the stated attenuation
on the full frequency band and a full-mass translated interval for every label.
Nonnegative digit starting indices are supplied later by the packing inequalities.
-/

open MeasureTheory
open scoped BigOperators ENNReal
open LpSelfSimilar.Entropy LpSelfSimilar.FiniteProbability LpSelfSimilar.Fourier
open LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- The original mass of a label in the maximizing decomposition of the actual digit law. -/
noncomputable def digitBandLabelWeight (θ : ℝ) (n : ℕ) (j : ℝ)
    (label : Finset (digitPMF_support_finite θ n).toFinset) : ℝ :=
  jointLabelWeight ((digitBandFamily θ n).joint j) label

/-- The actual conditional probability measure, with the proved null-label convention. -/
noncomputable def digitBandConditionalLaw (θ : ℝ) (n : ℕ) (j : ℝ)
    (label : Finset (digitPMF_support_finite θ n).toFinset) : Measure ℝ :=
  jointConditionalLaw ((digitBandFamily θ n).joint j) ((digitBandFamily θ n).supported j).1
    (fun x ↦ (x : ℝ)) label

/-- An actual geometric pushforward of the conditional digit measure. -/
noncomputable def digitBandShiftedLaw (θ : ℝ) (n : ℕ) (j : ℝ) (m : ℤ)
    (label : Finset (digitPMF_support_finite θ n).toFinset) : Measure ℝ :=
  (digitBandConditionalLaw θ n j label).map (fun x ↦ θ ^ m * x)

instance digitBandConditionalLaw_isProbabilityMeasure (θ : ℝ) (n : ℕ) (j : ℝ)
    (label : Finset (digitPMF_support_finite θ n).toFinset) :
    IsProbabilityMeasure (digitBandConditionalLaw θ n j label) := by
  unfold digitBandConditionalLaw
  infer_instance

instance digitBandShiftedLaw_isProbabilityMeasure (θ : ℝ) (n : ℕ) (j : ℝ) (m : ℤ)
    (label : Finset (digitPMF_support_finite θ n).toFinset) :
    IsProbabilityMeasure (digitBandShiftedLaw θ n j m label) := by
  unfold digitBandShiftedLaw digitBandConditionalLaw
  rw [jointConditionalLaw_map_mul]
  infer_instance

/-- Every shifted conditional digit law, including null labels, has total mass one. -/
theorem digitBandShiftedLaw_univ (θ : ℝ) (n : ℕ) (j : ℝ) (m : ℤ)
    (label : Finset (digitPMF_support_finite θ n).toFinset) :
    digitBandShiftedLaw θ n j m label Set.univ = 1 := measure_univ

/-- The original digit PMF is exactly the mixture of its maximizing conditional laws. -/
theorem digitPMF_eq_band_mixture (θ : ℝ) (n : ℕ) (j : ℝ) :
    (digitPMF θ n).toMeasure =
      ∑ label, ENNReal.ofReal (digitBandLabelWeight θ n j label) •
        digitBandConditionalLaw θ n j label := by
  classical
  rw [← realVectorLaw_on_support_eq_toMeasure (digitPMF θ n) (digitPMF_support_finite θ n)]
  exact realVectorLaw_eq_jointConditional_mixture _ _ _ _
    ((digitBandFamily θ n).supported j) (fun x ↦ (x : ℝ))

/-- The weighted characteristic-function norms equal the proved conditional Fourier expression. -/
theorem digitBandShiftedLaw_charFun_norm_average (θ : ℝ) (n : ℕ) (j : ℝ) (m : ℤ) (s : ℝ) :
    (∑ label, digitBandLabelWeight θ n j label *
      ‖charFun (digitBandShiftedLaw θ n j m label) s‖) =
      jointExpectedTransformNorm ((digitBandFamily θ n).joint j)
        (fun x ↦ θ ^ m * (x : ℝ)) s := by
  simp only [digitBandLabelWeight, digitBandShiftedLaw, digitBandConditionalLaw,
    jointConditionalLaw_map_mul]
  exact sum_weighted_norm_charFun_jointConditionalLaw _
    ((digitBandFamily θ n).supported j).1 (fun x ↦ θ ^ m * (x : ℝ)) s

/-- One actual shifted digit block has the exact attenuation and translated support properties. -/
theorem exists_digit_band_block {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 70) (n : ℕ) (j : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ k : Fin (geometricPhaseLength θ + 1),
      let m := bandFirstShift θ ((2 : ℝ) ^ (-j)) r + (k.val : ℤ)
      (∀ ξ ε : ℝ, abs (|ξ| - 1) ≤ ε →
        (∑ label, digitBandLabelWeight θ n j label *
          ‖charFun (digitBandShiftedLaw θ n j m label) (ξ / r)‖) ≤
            1 - digitBandCancellation θ n j + 52 * ε) ∧
      (∀ label, ∃ b : ℝ,
        ((digitBandShiftedLaw θ n j m label).map (fun x ↦ x - b)) (Set.Icc 0 (52 * r)) = 1) := by
  classical
  obtain ⟨k, hfreq, hsupp⟩ := (digitBandFamily θ n).exists_shift_with_frequency_control
    (sum_digit_support_toReal θ n) j hθ0 hθ1 hgap hr
  let m := bandFirstShift θ ((2 : ℝ) ^ (-j)) r + (k.val : ℤ)
  refine ⟨k, ?_, ?_⟩
  · intro ξ ε hξ
    rw [digitBandShiftedLaw_charFun_norm_average]
    exact hfreq ξ ε hξ
  · intro label
    have hdiam : ∀ i, jointConditionalWeight ((digitBandFamily θ n).joint j) label i ≠ 0 →
        ∀ l, jointConditionalWeight ((digitBandFamily θ n).joint j) label l ≠ 0 →
          |θ ^ m * (i : ℝ) - θ ^ m * (l : ℝ)| ≤ 52 * r := by
      obtain ⟨b, hb⟩ := hsupp label
      intro i hi l hl
      have hbi := hb i hi
      have hbl := hb l hl
      apply abs_le.mpr
      constructor <;> linarith
    have h := jointConditionalLaw_exists_translated_interval
      ((digitBandFamily θ n).joint j) ((digitBandFamily θ n).supported j).1
      (fun x ↦ θ ^ m * (x : ℝ)) label (by positivity) hdiam
    simpa only [digitBandShiftedLaw, digitBandConditionalLaw, jointConditionalLaw_map_mul] using h

end LpSelfSimilar.Bernoulli
