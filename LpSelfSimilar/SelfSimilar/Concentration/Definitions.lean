module

public import LpSelfSimilar.Geometry.PositiveAffine
public import LpSelfSimilar.SelfSimilar.StoppingWords

@[expose] public section

/-!
# The normalized two-map system and concentration of an interval

The two maps are theta*x and theta*x+1-theta, with equal weights.
Stationarity is an equality of actual mapped measures. An interval is
concentrated when E occupies strictly more than the prescribed fraction
of its Lebesgue volume. No separation of the image intervals is assumed.
-/

open MeasureTheory Set
open LpSelfSimilar.Geometry
open scoped ENNReal

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- The actual normalized Bernoulli digit map. -/
def digitMap {θ : ℝ} (hθ : 0 < θ) (e : Bool) : PositiveAffine :=
  ⟨θ, if e then 1 - θ else 0, hθ⟩

/-- Equal-weight stationarity for the two normalized affine maps. -/
def IsStationary {θ : ℝ} (hθ : 0 < θ) (μ : Measure ℝ) : Prop :=
  μ = ∑ e : Bool, (1 / 2 : ℝ≥0∞) • μ.map (digitMap hθ e)

/-- The strict concentration test used to stop a cylinder interval. -/
def IsConcentrated (E : Set ℝ) (r : ℝ) (q : PositiveAffine) : Prop :=
  ENNReal.ofReal r * volume q.interval < volume (E ∩ q.interval)

/-- The image of either digit map lies inside the unit interval. -/
theorem digitMap_interval_subset {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (e : Bool) :
    (digitMap hθ e).interval ⊆ Icc 0 1 := by
  intro x hx
  cases e <;> dsimp [digitMap, PositiveAffine.interval] at hx ⊢ <;>
    rcases hx with ⟨hx0, hx1⟩ <;> constructor <;> linarith

/-- The stationarity equality evaluated on a measurable set. -/
theorem stationary_apply {θ : ℝ} {hθ : 0 < θ} {μ : Measure ℝ}
    (hμ : IsStationary hθ μ) {E : Set ℝ} (hE : MeasurableSet E) :
    μ E = ∑ e : Bool, (1 / 2 : ℝ≥0∞) * μ ((digitMap hθ e) ⁻¹' E) := by
  conv_lhs => rw [hμ]
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro e he
  rw [Measure.smul_apply, Measure.map_apply (digitMap hθ e).measurable hE]
  rfl

/-- Failure of concentration is exactly the non-strict volume bound. -/
theorem not_isConcentrated_iff (E : Set ℝ) (r : ℝ) (q : PositiveAffine) :
    ¬IsConcentrated E r q ↔ volume (E ∩ q.interval) ≤ ENNReal.ofReal r * volume q.interval := by
  exact not_lt

end LpSelfSimilar.SelfSimilar.Concentration
