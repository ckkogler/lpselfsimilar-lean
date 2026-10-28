module

public import LpSelfSimilar.Algebraic.EntropyRate
public import LpSelfSimilar.Gaussian.BinaryDifferentialEntropy

@[expose] public section

/-!
# The entropy-rate comparison in differential-entropy form

The canonical finite-channel information has already been identified with a
difference of finite differential entropies. Its Gaussian rate comparison can
therefore be written using the actual binary Gaussian output laws directly.
No differential-entropy identity or integrability is an input hypothesis.
-/

open Real Set
open LpSelfSimilar.Bernoulli LpSelfSimilar.Gaussian LpSelfSimilar.Entropy

namespace LpSelfSimilar.Algebraic

/-- The actual differential-entropy gain at every amplitude is bounded by the unit digit rate. -/
theorem unit_entropyRate_ge_differentialEntropy_gain {x : ℝ} (hx : IsAlgebraicUnit x)
    (hx0 : 0 < x) (hx1 : x < 1) (u : ℝ) :
    differentialEntropy (binaryGaussianLaw (u * mahlerMeasure x)) -
        differentialEntropy (binaryGaussianLaw u) ≤ entropyRate x := by
  have h := unit_entropyRate_ge_binary_information hx hx0 hx1 u
  simp only [binaryGaussianInformation_eq_differentialEntropy_sub] at h
  linarith

/-- The differential-entropy gain family has a proved finite upper bound. -/
theorem unit_differentialEntropy_gains_bddAbove {x : ℝ} (hx : IsAlgebraicUnit x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    BddAbove ((fun u : ℝ => differentialEntropy (binaryGaussianLaw (u * mahlerMeasure x)) -
      differentialEntropy (binaryGaussianLaw u)) '' Ioi 0) := by
  refine ⟨entropyRate x, ?_⟩
  rintro _ ⟨u, _, rfl⟩
  exact unit_entropyRate_ge_differentialEntropy_gain hx hx0 hx1 u

/-- The full positive-amplitude supremum comparison, expressed with canonical differential entropy. -/
theorem unit_entropyRate_ge_sup_differentialEntropy {x : ℝ} (hx : IsAlgebraicUnit x)
    (hx0 : 0 < x) (hx1 : x < 1) :
    sSup ((fun u : ℝ => differentialEntropy (binaryGaussianLaw (u * mahlerMeasure x)) -
      differentialEntropy (binaryGaussianLaw u)) '' Ioi 0) ≤ entropyRate x := by
  apply csSup_le
  · exact ⟨_, ⟨1, by norm_num, rfl⟩⟩
  · rintro _ ⟨u, _, rfl⟩
    exact unit_entropyRate_ge_differentialEntropy_gain hx hx0 hx1 u

end LpSelfSimilar.Algebraic
