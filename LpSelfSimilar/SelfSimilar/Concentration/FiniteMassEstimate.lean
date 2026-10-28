module

public import LpSelfSimilar.SelfSimilar.Concentration.BoundaryResidual
public import LpSelfSimilar.SelfSimilar.Concentration.StoppedCover

@[expose] public section

/-!
# The concentration estimate at every finite stopping horizon

Concentrated terminal intervals spend their conditional mass budget on the
finite cover. Every other terminal interval spends its E-mass on the shrinking
inner boundary layer. Summing the exact stopped decomposition gives a finite
measure inequality; the residual will then tend to zero for open E.
-/

open MeasureTheory Set
open LpSelfSimilar.Geometry
open scoped ENNReal

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- A set of volume at most r does not concentrate the initial unit interval. -/
theorem not_concentrated_identity_of_volume_le {E : Set ℝ} {r : ℝ}
    (hv : volume E ≤ ENNReal.ofReal r) : ¬IsConcentrated E r PositiveAffine.identity := by
  apply (not_isConcentrated_iff E r PositiveAffine.identity).mpr
  calc
    _ ≤ volume E := measure_mono inter_subset_left
    _ ≤ ENNReal.ofReal r := hv
    _ = _ := by rw [PositiveAffine.volume_interval]; simp [PositiveAffine.identity]

/-- At each finite horizon, E-mass is bounded by the concentrated-cover budget plus boundary mass. -/
theorem finite_stopped_mass_estimate {θ r K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 ≤ r) (hr1 : r < 1)
    (hK : 0 ≤ K) (he : 0 ≤ e) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : IsStationary hθ μ) (hsupp : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hbound : ∀ A : Set ℝ, MeasurableSet A →
      μ A ≤ ENNReal.ofReal K * volume A + ENNReal.ofReal e)
    {E : Set ℝ} (hE : MeasurableSet E) (hv : volume E ≤ ENNReal.ofReal r) (n : ℕ) :
    μ E ≤ ENNReal.ofReal (K * (r / θ) + e) * μ (stoppedCover hθ E r n) +
      μ (innerBoundaryLayer E (θ ^ n)) := by
  let β := ENNReal.ofReal (K * (r / θ) + e)
  let q := fun w : Word Bool n => stoppedMap hθ E r n PositiveAffine.identity w
  have hroot := not_concentrated_identity_of_volume_le hv
  have hterm (w : Word Bool n) : μ (q w ⁻¹' E) ≤
      β * μ (q w ⁻¹' stoppedCover hθ E r n) +
      μ (q w ⁻¹' innerBoundaryLayer E (θ ^ n)) := by
    by_cases hc : IsConcentrated E r (q w)
    · rw [preimage_stoppedCover_mass_eq_one hθ μ hsupp E r n w hc, mul_one]
      exact (concentrated_stopped_preimage_mass_le hθ hθ1 hr hK he μ hsupp hbound hE
        n PositiveAffine.identity (fun h => False.elim (hroot h)) w hc).trans (le_self_add)
    · exact (stopped_preimage_mass_le_boundaryLayer_of_not_concentrated
        hθ hr hr1 μ hsupp E n w hc).trans (le_add_self)
  have hd (A : Set ℝ) (hA : MeasurableSet A) :
      (∑ w : Word Bool n, (1 / 2 : ℝ≥0∞) ^ n * μ (q w ⁻¹' A)) = μ A := by
    calc
      _ = μ (PositiveAffine.identity ⁻¹' A) := stopped_decomposition hθ hμ E r n _ hA
      _ = μ A := by
        congr 1
        ext x
        change (1 * x + 0 ∈ A) ↔ x ∈ A
        simp
  calc
    μ E = ∑ w : Word Bool n, (1 / 2 : ℝ≥0∞) ^ n * μ (q w ⁻¹' E) := (hd E hE).symm
    _ ≤ ∑ w : Word Bool n, (1 / 2 : ℝ≥0∞) ^ n *
        (β * μ (q w ⁻¹' stoppedCover hθ E r n) +
          μ (q w ⁻¹' innerBoundaryLayer E (θ ^ n))) :=
      Finset.sum_le_sum (fun w _ => mul_le_mul' le_rfl (hterm w))
    _ = _ := by
      rw [← hd (stoppedCover hθ E r n) (measurableSet_stoppedCover hθ E r n),
        ← hd (innerBoundaryLayer E (θ ^ n)) (measurableSet_innerBoundaryLayer hE _),
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w hw
      dsimp only [β]
      ring

end LpSelfSimilar.SelfSimilar.Concentration
