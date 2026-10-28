module

public import LpSelfSimilar.Gaussian.LinearGaussian
public import LpSelfSimilar.Analysis.MatrixCovariancePowers
public import LpSelfSimilar.Entropy.AdditiveInformationChain
public import LpSelfSimilar.Entropy.SignalEntropyBound

@[expose] public section

/-!
Finite-signal information at matrix Gaussian scales.

The covariance order is converted into an actual independent Gaussian residual
law before using information data processing. We obtain scale monotonicity and
the independent-summand inequality, including singular residuals. The finite
power-scale telescope is bounded by the entropy of the actual signal law.
These are the finite-noise-scale ingredients of the unit-entropy argument.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Matrix
open scoped MatrixOrder

namespace LpSelfSimilar.Gaussian

noncomputable def matrixInformation {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (X : Ω → EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) : ℝ :=
  Entropy.additiveInformation p X (linearGaussian A)

lemma matrixInformation_nonneg {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (X : Ω → EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) :
    0 ≤ matrixInformation p X A := Entropy.additiveInformation_nonneg p X _

lemma matrixInformation_le_signal_entropy {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (X : Ω → EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) :
    matrixInformation p X A ≤ Entropy.finiteEntropy (p.map X)
      (by simpa using (Set.toFinite p.support).image X) :=
  Entropy.additiveInformation_le_signal_entropy p X _

/-- Increasing the Gaussian covariance decreases finite-signal information. -/
theorem matrixInformation_covariance_antitone {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (X : Ω → EuclideanSpace ℝ ι) (A B : Matrix ι ι ℝ)
    (hAB : A * Aᴴ ≤ B * Bᴴ) : matrixInformation p X B ≤ matrixInformation p X A := by
  have h := Entropy.additiveInformation_conv_le p X (linearGaussian A)
    (multivariateGaussian 0 (B * Bᴴ - A * Aᴴ))
  rwa [linearGaussian_residual A B hAB] at h

/-- Adding an independent finite summand increases the information difference
between ordered matrix Gaussian scales. -/
theorem matrixInformation_difference_add_summand {Ω Ξ ι : Type*}
    [Fintype Ω] [Fintype Ξ] [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (p : PMF Ω) (q : PMF Ξ) (X : Ω → EuclideanSpace ℝ ι) (Y : Ξ → EuclideanSpace ℝ ι)
    (A B : Matrix ι ι ℝ) (hAB : A * Aᴴ ≤ B * Bᴴ) :
    matrixInformation q Y A - matrixInformation q Y B ≤
      matrixInformation (pairPMF p q) (fun z ↦ X z.1 + Y z.2) A -
        matrixInformation (pairPMF p q) (fun z ↦ X z.1 + Y z.2) B := by
  have h := Entropy.additiveInformation_noise_difference_mono p q X Y (linearGaussian A)
    (multivariateGaussian 0 (B * Bᴴ - A * Aᴴ))
  rwa [linearGaussian_residual A B hAB] at h

lemma matrixInformation_power_monotone {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (X : Ω → EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ)
    (hA : A * Aᴴ ≤ 1) : Monotone (fun n : ℕ ↦ matrixInformation p X (A ^ n)) := by
  intro m n hmn
  exact matrixInformation_covariance_antitone p X _ _
    (matrix_power_covariance_antitone A hA hmn)

/-- Exact finite telescope; no limiting entropy or rate is assumed. -/
theorem matrixInformation_power_telescope {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (X : Ω → EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n,
        (matrixInformation p X (A ^ (j + 1)) - matrixInformation p X (A ^ j)) =
      matrixInformation p X (A ^ n) - matrixInformation p X 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- The telescope is controlled by the actual finite signal entropy, with all
collisions merged. This is the upper half of the finite-digit entropy proof. -/
theorem matrixInformation_power_telescope_le_entropy {Ω ι : Type*} [Fintype Ω] [Fintype ι]
    [DecidableEq ι] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (X : Ω → EuclideanSpace ℝ ι) (A : Matrix ι ι ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range n,
        (matrixInformation p X (A ^ (j + 1)) - matrixInformation p X (A ^ j)) ≤
      Entropy.finiteEntropy (p.map X) (by simpa using (Set.toFinite p.support).image X) := by
  rw [matrixInformation_power_telescope]
  exact (sub_le_self _ (matrixInformation_nonneg p X 1)).trans
    (matrixInformation_le_signal_entropy p X (A ^ n))

end LpSelfSimilar.Gaussian
