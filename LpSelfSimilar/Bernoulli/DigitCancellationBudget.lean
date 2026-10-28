module

public import LpSelfSimilar.Entropy.ExplicitCancellationBudget
public import LpSelfSimilar.Bernoulli.DigitBandEntropy

@[expose] public section

/-!
# Cancellation budgets for actual Bernoulli digit laws

Choose an actual maximizing band family on the merged support of each digit PMF.
The cancellation retains the family and its original label marginal. Its exact
range, measurability and finite-n budget connect the entropy argument to the
conditional digit laws used in the subsequent phase and block construction.
-/

open MeasureTheory Set LpSelfSimilar.Entropy
open scoped BigOperators

namespace LpSelfSimilar.Bernoulli

/-- An actual measurable maximizing joint family on the merged finite digit support. -/
noncomputable def digitBandFamily (θ : ℝ) (n : ℕ) :
    MaximizingBandFamily
      (fun x : (digitPMF_support_finite θ n).toFinset ↦ (x : ℝ))
      (fun x ↦ (digitPMF θ n x).toReal) :=
  Classical.choice (nonempty_maximizingBandFamily _ _ (fun _ ↦ ENNReal.toReal_nonneg))

/-- Expected cancellation under the original label probabilities at dyadic exponent `j`. -/
noncomputable def digitBandCancellation (θ : ℝ) (n : ℕ) (j : ℝ) : ℝ :=
  (digitBandFamily θ n).cancellation j

/-- The real weights on actual digit atoms sum to one, independently of word collisions. -/
theorem sum_digit_support_toReal (θ : ℝ) (n : ℕ) :
    ∑ x : (digitPMF_support_finite θ n).toFinset, (digitPMF θ n x).toReal = 1 := by
  let hp := digitPMF_support_finite θ n
  change (∑ x ∈ hp.toFinset.attach, (digitPMF θ n x.val).toReal) = 1
  rw [Finset.sum_attach hp.toFinset (fun x : ℝ ↦ (digitPMF θ n x).toReal)]
  exact sum_support_toReal (digitPMF θ n) hp

/-- The scale-dependent cancellation of the selected digit decompositions is measurable. -/
theorem measurable_digitBandCancellation (θ : ℝ) (n : ℕ) : Measurable (digitBandCancellation θ n) :=
  (digitBandFamily θ n).measurable_cancellation

/-- The exact cancellation range, including all null labels. -/
theorem digitBandCancellation_mem_Icc (θ : ℝ) (n : ℕ) (j : ℝ) :
    digitBandCancellation θ n j ∈ Icc 0 (1 - Real.sqrt (7 / 16)) :=
  (digitBandFamily θ n).cancellation_mem_Icc (sum_digit_support_toReal θ n) j

/-- The expected digit cancellation is integrable on every bounded scale interval. -/
theorem intervalIntegrable_digitBandCancellation (θ : ℝ) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (digitBandCancellation θ n) volume a b :=
  (digitBandFamily θ n).intervalIntegrable_cancellation (sum_digit_support_toReal θ n) a b

/-- Exact finite-n integrated cancellation bound with the original digit-law hypotheses. -/
theorem digit_band_cancellation_integral_lower_bound
    (θ ρ L : ℝ) (n : ℕ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hentropy : ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ x ∈ (digitPMF θ n).support, ∀ y ∈ (digitPMF θ n).support, x ≠ y →
      (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    n * bandCancellationRate ρ L -
        (4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) +
          4 * cancellationRemainder (L / ρ)) / cancellationSlope (L / ρ) ≤
      ∫ j in (4 / 25 : ℝ) * ρ * n..L * n + 4, digitBandCancellation θ n j := by
  let hp := digitPMF_support_finite θ n
  have hentropy' : ρ * n ≤
      (∑ x : hp.toFinset, Real.negMulLog (digitPMF θ n x).toReal) / Real.log 2 := by
    change ρ * n ≤
      (∑ x ∈ hp.toFinset.attach, Real.negMulLog (digitPMF θ n x.val).toReal) / Real.log 2
    rw [Finset.sum_attach hp.toFinset (fun x : ℝ ↦ Real.negMulLog (digitPMF θ n x).toReal)]
    exact hentropy
  refine (digitBandFamily θ n).cancellation_integral_lower_bound_explicit
    (sum_digit_support_toReal θ n) θ ρ L n hθ1 hρ hρ1 hL ?_ hentropy' ?_
  · intro x
    simpa only [one_div] using abs_le.mpr
      (digitPMF_support_subset_interval hθ0 hθ1 n (hp.mem_toFinset.mp x.property))
  · intro x y hxy
    exact hsep x (hp.mem_toFinset.mp x.property) y (hp.mem_toFinset.mp y.property)
      (fun he ↦ hxy (Subtype.ext he))

end LpSelfSimilar.Bernoulli
