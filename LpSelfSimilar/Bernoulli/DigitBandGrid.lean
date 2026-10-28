module

public import LpSelfSimilar.Bernoulli.DigitCancellationBudget
public import LpSelfSimilar.Analysis.ClippedGridBudget

@[expose] public section

/-!
# A finite grid retaining the actual Bernoulli cancellation budget

For each block length, clip the proved cancellation by the uniform frequency
loss `52*epsilon`. Averaging a finite translated grid supplies a deterministic
choice whose retained attenuation has the exact finite-length integral bound.
The subsequent packing estimates specify its spacing and number of candidates.
-/

open MeasureTheory Set
open scoped BigOperators
open LpSelfSimilar.Entropy LpSelfSimilar.Analysis

namespace LpSelfSimilar.Bernoulli

/-- Attenuation remaining after the uniform loss on the frequency band. -/
noncomputable def digitGridAttenuation (θ ε : ℝ) (n : ℕ) (j : ℝ) : ℝ :=
  max (digitBandCancellation θ n j - 52 * ε) 0

/-- Clipping retains measurability, so the finite averaging theorem applies. -/
theorem measurable_digitGridAttenuation (θ ε : ℝ) (n : ℕ) :
    Measurable (digitGridAttenuation θ ε n) :=
  ((measurable_digitBandCancellation θ n).sub measurable_const).max measurable_const

/-- The clipped actual cancellation lies between zero and one. -/
theorem digitGridAttenuation_mem_Icc (θ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) (j : ℝ) :
    digitGridAttenuation θ ε n j ∈ Icc 0 1 := by
  have hd := digitBandCancellation_mem_Icc θ n j
  refine ⟨le_max_right _ _, max_le ?_ zero_le_one⟩
  nlinarith [hd.2, Real.sqrt_nonneg (7 / 16 : ℝ)]

/-- A finite translated grid retains the exact cancellation budget after clipping. -/
theorem exists_digit_grid_budget
    (θ ρ L : ℝ) (n : ℕ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hentropy : ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ x ∈ (digitPMF θ n).support, ∀ y ∈ (digitPMF θ n).support, x ≠ y →
      (2 : ℝ) ^ (-(L * n)) ≤ |x - y|)
    {ε h : ℝ} (hε : 0 ≤ ε) (hh : 0 < h) (N : ℕ) (hN : L * n + 4 ≤ h * N) :
    ∃ t : ℝ,
      (n * (bandCancellationRate ρ L - 52 * ε * L) -
        (4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) +
          4 * cancellationRemainder (L / ρ)) / cancellationSlope (L / ρ) - 208 * ε) / h ≤
      ∑ j ∈ Finset.range N,
        if h * ((j : ℝ) + t) ∈ Icc ((4 / 25 : ℝ) * ρ * n) (L * n + 4) then
          digitGridAttenuation θ ε n (h * ((j : ℝ) + t)) else 0 := by
  classical
  have ha : 0 ≤ (4 / 25 : ℝ) * ρ * n := by positivity
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hab : (4 / 25 : ℝ) * ρ * n ≤ L * n + 4 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ L - (4 / 25 : ℝ) * ρ) hn]
  have hf : ∀ j, 0 ≤ digitBandCancellation θ n j ∧ digitBandCancellation θ n j ≤ 1 := by
    intro j
    have hd := digitBandCancellation_mem_Icc θ n j
    exact ⟨hd.1, by nlinarith [hd.2, Real.sqrt_nonneg (7 / 16 : ℝ)]⟩
  obtain ⟨t, ht⟩ := exists_shifted_grid_clipped_budget
    (digitBandCancellation θ n) (measurable_digitBandCancellation θ n) hf
    ha hab hh (by positivity : 0 ≤ 52 * ε) N hN
    (intervalIntegrable_digitBandCancellation θ n _ _)
    (digit_band_cancellation_integral_lower_bound θ ρ L n hθ0 hθ1 hρ hρ1 hL hentropy hsep)
  refine ⟨t, le_trans ?_ ht⟩
  apply div_le_div_of_nonneg_right _ hh.le
  nlinarith [mul_nonneg (by positivity : 0 ≤ 52 * ε) ha]

end LpSelfSimilar.Bernoulli
