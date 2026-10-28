module

public import LpSelfSimilar.SelfSimilar.Concentration.FiniteMassEstimate

@[expose] public section

/-!
# Removing the finite-horizon residual for open sets

The finite stopped cover has volume at most 3*volume(E)/r. The finite-horizon
measure estimate is therefore bounded by a fixed small-set mass modulus plus
a shrinking boundary layer. Continuity of finite measure from above removes
the latter. At r=theta*e/K, the resulting coefficient is exactly 2*e.
-/

open MeasureTheory Set Filter
open LpSelfSimilar.Geometry
open scoped ENNReal Topology

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- Finite volume forces a real set to have nonempty complement. -/
theorem complement_nonempty_of_volume_le {E : Set ℝ} {r : ℝ}
    (hv : volume E ≤ ENNReal.ofReal r) : Eᶜ.Nonempty := by
  by_contra h
  have hE : E = Set.univ := by
    ext x
    simp only [mem_univ, iff_true]
    by_contra hx
    exact h ⟨x, hx⟩
  rw [hE, Real.volume_univ] at hv
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hv)

/-- The exact open-set concentration estimate, with no residual term. -/
theorem open_set_mass_le_concentration_modulus {θ r K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hr : 0 < r) (hr1 : r < 1)
    (hK : 0 ≤ K) (he : 0 ≤ e) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : IsStationary hθ μ) (hsupp : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hbound : ∀ A : Set ℝ, MeasurableSet A →
      μ A ≤ ENNReal.ofReal K * volume A + ENNReal.ofReal e)
    {E : Set ℝ} (hE : IsOpen E) (hv : volume E ≤ ENNReal.ofReal r) :
    μ E ≤ ENNReal.ofReal (K * (r / θ) + e) *
      smallSetMass μ volume (ENNReal.ofReal (3 / r) * volume E) := by
  let b := ENNReal.ofReal (K * (r / θ) + e) *
    smallSetMass μ volume (ENNReal.ofReal (3 / r) * volume E)
  have ht := tendsto_measure_innerBoundaryLayer_pow μ hE
    (complement_nonempty_of_volume_le hv) hθ.le hθ1
  have hsum : Tendsto (fun n : ℕ => b + μ (innerBoundaryLayer E (θ ^ n))) atTop (𝓝 b) := by
    simpa only [add_zero] using tendsto_const_nhds.add ht
  apply ge_of_tendsto hsum
  apply Filter.Eventually.of_forall
  intro n
  exact (finite_stopped_mass_estimate hθ hθ1.le hr.le hr1 hK he μ hμ hsupp
    hbound hE.measurableSet hv n).trans (add_le_add
      (mul_le_mul' le_rfl (stoppedCover_mass_le_smallSetMass hθ hr μ hE.measurableSet n)) le_rfl)

/-- The stopping level theta*e/K gives the exact coefficient 2*e in the open-set modulus estimate. -/
theorem open_set_mass_le_twice_error_modulus {θ K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hK : 0 < K) (he : 0 < e)
    (hr1 : θ * (e / K) < 1) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : IsStationary hθ μ) (hsupp : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hbound : ∀ A : Set ℝ, MeasurableSet A →
      μ A ≤ ENNReal.ofReal K * volume A + ENNReal.ofReal e)
    {E : Set ℝ} (hE : IsOpen E) (hv : volume E ≤ ENNReal.ofReal (θ * (e / K))) :
    μ E ≤ ENNReal.ofReal (2 * e) *
      smallSetMass μ volume (ENNReal.ofReal (3 / (θ * (e / K))) * volume E) := by
  have h := open_set_mass_le_concentration_modulus hθ hθ1 (mul_pos hθ (div_pos he hK))
    hr1 hK.le he.le μ hμ hsupp hbound hE hv
  have heq : K * (θ * (e / K) / θ) + e = 2 * e := by
    field_simp [hθ.ne', hK.ne']
    <;> ring
  rwa [heq] at h

end LpSelfSimilar.SelfSimilar.Concentration
