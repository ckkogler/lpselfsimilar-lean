module

public import LpSelfSimilar.Fourier.FiniteTransform
public import LpSelfSimilar.Probability.RealProbabilityVector
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

/-!
# Finite Fourier sums are characteristic functions of actual laws

The real-vector construction is an ordinary PMF mapped to real atom locations.
Its weighted Bochner integral identifies Mathlib's characteristic function with
the finite exponential sum used throughout the cancellation estimates.
-/

open MeasureTheory
open scoped BigOperators

namespace LpSelfSimilar.Fourier

/-- The finite transform is exactly the characteristic function of the mapped probability measure. -/
theorem charFun_realVectorLaw {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (s : ℝ) :
    charFun (FiniteProbability.realVectorLaw p hp hsum z) s = finiteTransform p z s := by
  rw [charFun_apply_real,
    FiniteProbability.integral_realVectorLaw p hp hsum z _ (by fun_prop)]
  simp only [finiteTransform, Complex.real_smul, Complex.ofReal_mul]

end LpSelfSimilar.Fourier
