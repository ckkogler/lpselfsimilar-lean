module

public import LpSelfSimilar.Fourier.FiniteTransform
public import LpSelfSimilar.Analysis.WeightedAverages
public import LpSelfSimilar.Entropy.SixteenAtomCancellation

@[expose] public section

/-!
# From averaged phase separation to finite Fourier cancellation

A lower bound for every off-diagonal phase deficit bounds the averaged squared
Fourier norm by the collision probability. Weighted Cauchy--Schwarz then gives
the exact cancellation functional. Phase hypotheses are required only at
nonzero-weight atoms, so conditional vectors may retain their zero coordinates.
-/

open scoped BigOperators

namespace LpSelfSimilar.Fourier

/-- Averaging the pairwise identity commutes with both finite atom sums. -/
theorem weighted_sq_norm_finiteTransform_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p z : ι → ℝ) (w s : κ → ℝ) (hp : ∑ i, p i = 1) (hw : ∑ k, w k = 1) :
    (∑ k, w k * ‖finiteTransform p z (s k)‖ ^ 2) =
      1 - ∑ i, ∑ j, p i * p j *
        ∑ k, w k * (1 - Real.cos (s k * (z i - z j))) := by
  have hterm (k : κ) : w k * ‖finiteTransform p z (s k)‖ ^ 2 =
      w k - w k * (∑ i, ∑ j, p i * p j *
        (1 - Real.cos (s k * (z i - z j)))) := by
    rw [sq_norm_finiteTransform_eq_one_sub p z (s k) hp]
    ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, hw]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Uniform off-diagonal phase cancellation controls the averaged second moment. -/
theorem weighted_sq_norm_finiteTransform_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p z : ι → ℝ) (w s : κ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (hwsum : ∑ k, w k = 1) (γ : ℝ)
    (hphase : ∀ i j, i ≠ j → p i ≠ 0 → p j ≠ 0 →
      γ ≤ ∑ k, w k * (1 - Real.cos (s k * (z i - z j)))) :
    (∑ k, w k * ‖finiteTransform p z (s k)‖ ^ 2) ≤
      1 - γ + γ * ∑ i, (p i) ^ 2 := by
  classical
  have hpoint (i j : ι) : γ * p i * p j ≤
      p i * p j * (∑ k, w k * (1 - Real.cos (s k * (z i - z j)))) +
        if i = j then γ * (p i) ^ 2 else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [sub_self, mul_zero, Real.cos_zero, Finset.sum_const_zero,
        ite_true, zero_add]
      nlinarith
    · by_cases hi : p i = 0
      · simp [hi, hij]
      by_cases hj : p j = 0
      · simp [hj, hij]
      simp only [hij, ite_false, add_zero]
      have h := mul_le_mul_of_nonneg_left (hphase i j hij hi hj)
        (mul_nonneg (hp i) (hp j))
      nlinarith
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun i hi ↦
    Finset.sum_le_sum (s := Finset.univ) (fun j hj ↦ hpoint i j))
  have hmass : (∑ i, ∑ j, γ * p i * p j) = γ := by
    simp_rw [← Finset.mul_sum, hpsum, mul_one]
    rw [← Finset.mul_sum, hpsum, mul_one]
  have hdiagonal : (∑ i, ∑ j, if i = j then γ * (p i) ^ 2 else 0) =
      γ * ∑ i, (p i) ^ 2 := by
    simp [Finset.mul_sum]
  simp only [Finset.sum_add_distrib] at htotal
  rw [hmass, hdiagonal] at htotal
  rw [weighted_sq_norm_finiteTransform_eq p z w s hpsum hwsum]
  linarith

/-- The `3/5` phase estimate gives exactly one minus the finite cancellation functional. -/
theorem weighted_norm_finiteTransform_le_one_sub_cancellation
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p z : ι → ℝ) (w s : κ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hpsum : ∑ i, p i = 1) (hw : ∀ k, 0 ≤ w k) (hwsum : ∑ k, w k = 1)
    (hphase : ∀ i j, i ≠ j → p i ≠ 0 → p j ≠ 0 →
      (3 / 5 : ℝ) ≤ ∑ k, w k * (1 - Real.cos (s k * (z i - z j)))) :
    (∑ k, w k * ‖finiteTransform p z (s k)‖) ≤
      1 - Entropy.finiteCancellation Finset.univ p := by
  have hs := weighted_sq_norm_finiteTransform_le p z w s hp hpsum hwsum (3 / 5) hphase
  have hB : (∑ k, w k * ‖finiteTransform p z (s k)‖ ^ 2) ≤
      2 / 5 + (3 / 5) * ∑ i, (p i) ^ 2 := by linarith
  have h := Analysis.weighted_sum_le_sqrt w (fun k ↦ ‖finiteTransform p z (s k)‖)
    hw hwsum hB
  simpa only [Entropy.finiteCancellation, sub_sub_cancel] using h

end LpSelfSimilar.Fourier
