module

public import LpSelfSimilar.SelfSimilar.Concentration.StoppedDecomposition
public import LpSelfSimilar.SelfSimilar.Concentration.ParentVolume
public import LpSelfSimilar.Geometry.ConcentratedIntervalCover

@[expose] public section

/-!
# Geometry and conditional mass of finite concentration stopping

Stopped intervals stay inside their initial interval. A terminal interval that
has not concentrated has used every available digit, so its length is exactly
theta^n times the initial length. Every concentrated stopped cylinder inherits
the conditional mass bound from its last nonconcentrated parent.
-/

open MeasureTheory Set
open LpSelfSimilar.Geometry
open scoped ENNReal

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- Every stopped interval lies inside the interval from which the procedure started. -/
theorem stoppedMap_interval_subset {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (E : Set ℝ) (r : ℝ) (n : ℕ) (q : PositiveAffine) (w : Word Bool n) :
    (stoppedMap hθ E r n q w).interval ⊆ q.interval := by
  classical
  induction n generalizing q with
  | zero => exact subset_rfl
  | succ n ih =>
    dsimp only [stoppedMap]
    split_ifs with hstop
    · exact subset_rfl
    · exact (ih _ _).trans (child_interval_subset hθ hθ1 q w.1)

/-- A terminal interval that is not concentrated has traversed every digit. -/
theorem stoppedMap_scale_eq_of_not_concentrated {θ : ℝ} (hθ : 0 < θ)
    (E : Set ℝ) (r : ℝ) (n : ℕ) (q : PositiveAffine) (w : Word Bool n)
    (hnot : ¬IsConcentrated E r (stoppedMap hθ E r n q w)) :
    (stoppedMap hθ E r n q w).scale = θ ^ n * q.scale := by
  classical
  induction n generalizing q with
  | zero => simp only [stoppedMap, pow_zero, one_mul]
  | succ n ih =>
    by_cases hq : IsConcentrated E r q
    · exfalso
      apply hnot
      simpa only [stoppedMap, hq, ↓reduceIte] using hq
    · simp only [stoppedMap, hq, ↓reduceIte] at hnot ⊢
      rw [ih _ _ hnot, child_scale, pow_succ]
      ring

/-- Every concentrated stopped interval has the conditional mass budget inherited from parent failure. -/
theorem concentrated_stopped_preimage_mass_le {θ r K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 ≤ r) (hK : 0 ≤ K) (he : 0 ≤ e)
    (μ : Measure ℝ) (hsupp : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hbound : ∀ A : Set ℝ, MeasurableSet A →
      μ A ≤ ENNReal.ofReal K * volume A + ENNReal.ofReal e)
    {E : Set ℝ} (hE : MeasurableSet E) (n : ℕ) (q : PositiveAffine)
    (hq : IsConcentrated E r q → μ (q ⁻¹' E) ≤ ENNReal.ofReal (K * (r / θ) + e))
    (w : Word Bool n) (hc : IsConcentrated E r (stoppedMap hθ E r n q w)) :
    μ ((stoppedMap hθ E r n q w) ⁻¹' E) ≤ ENNReal.ofReal (K * (r / θ) + e) := by
  classical
  induction n generalizing q with
  | zero => exact hq hc
  | succ n ih =>
    by_cases hstop : IsConcentrated E r q
    · simpa only [stoppedMap, hstop, ↓reduceIte] using hq hstop
    · simp only [stoppedMap, hstop, ↓reduceIte] at hc ⊢
      apply ih _ (fun _ => child_preimage_mass_le_of_parent_failure hθ hθ1 hr hK he
        μ hsupp hbound q w.1 hE hstop) _ hc

/-- Any finite family of concentrated affine intervals has the exact factor-three volume bound. -/
theorem volume_union_concentrated_affineIntervals_le {ι : Type*}
    (s : Finset ι) (q : ι → PositiveAffine) {E : Set ℝ}
    (hE : MeasurableSet E) {r : ℝ} (hr : 0 < r)
    (hc : ∀ i ∈ s, IsConcentrated E r (q i)) :
    volume (⋃ i ∈ s, (q i).interval) ≤ ENNReal.ofReal (3 / r) * volume E := by
  have h := volume_union_concentrated_closedBalls_le s
    (fun i => (q i).shift + (q i).scale / 2) (fun i => (q i).scale / 2)
    (fun i hi => (div_pos (q i).scale_pos (by norm_num)).le) hE hr (fun i hi => by
      rw [← (q i).interval_eq_closedBall]
      exact (hc i hi).le)
  simpa only [← PositiveAffine.interval_eq_closedBall] using h

end LpSelfSimilar.SelfSimilar.Concentration
