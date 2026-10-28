module

public import LpSelfSimilar.SelfSimilar.SmallSetEstimate
public import LpSelfSimilar.WeakReverseHolder.MeasureForm

@[expose] public section

/-!
An explicit small-set modulus supplies the quantitative input to Lemma 2.1.
This separates the arithmetic approximation estimates from the reusable
stopping-word proof of (2.2).
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar.SelfSimilar.System

lemma small_set_hypothesis_of_mass_bound {d : ℕ} {I : Type*} [Fintype I] [Nonempty I]
    (S : System d I) {ν : Measure (Space d)} [IsProbabilityMeasure ν]
    (hν : S.IsStationary ν) {K : Set (Space d)} (hKnull : ν Kᶜ = 0) (hKmass : ν K = 1)
    {a D ε η : ℝ} (ha : 0 < a) (ha1 : a < 1) (hmin : ∀ i, a ≤ (S.map i).ratio)
    (hD : 1 ≤ D) (hdiam : ∀ y ∈ K, ∀ z ∈ K, dist y z ≤ D)
    (hmod : smallSetMass ν volume (ENNReal.ofReal (smallSetConstant d a D * ε)) ≤
      ENNReal.ofReal η) : MeasureSmallSetHypothesis ν ε η := by
  intro x r hr hr1 E hE hsub hvol
  have hC : 0 < smallSetConstant d a D := smallSetConstant_pos ha (by linarith)
  have harg : ENNReal.ofReal (smallSetConstant d a D) *
      (volume E / volume (ball x r)) ≤ ENNReal.ofReal (smallSetConstant d a D * ε) := by
    calc
      _ ≤ ENNReal.ofReal (smallSetConstant d a D) * ENNReal.ofReal ε :=
        mul_le_mul' le_rfl ((ENNReal.div_le_iff (measure_ball_pos volume x hr).ne'
          measure_ball_ne_top).mpr hvol)
      _ = _ := (ENNReal.ofReal_mul hC.le).symm
  exact (S.small_set_estimate hν hKnull hKmass ha ha1 hmin hD hdiam x hr hr1 hE hsub).trans
    (mul_le_mul' ((smallSetMass_mono ν volume harg).trans hmod) le_rfl)

end LpSelfSimilar.SelfSimilar.System
