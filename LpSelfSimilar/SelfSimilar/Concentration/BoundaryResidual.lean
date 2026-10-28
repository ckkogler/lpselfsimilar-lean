module

public import LpSelfSimilar.SelfSimilar.Concentration.StoppedGeometry
public import LpSelfSimilar.Geometry.InnerBoundaryLayers

@[expose] public section

/-!
# Nonconcentrated terminal intervals lie in a shrinking boundary layer

When the concentration threshold is less than one, an interval contained in E
is necessarily concentrated. Thus a terminal interval which has not stopped
contains a point outside E. Its exact geometric length bounds the distance of
all its points in E from the complement. This argument does not require a
separation condition or a description of individual infinite digit paths.
-/

open MeasureTheory Set Metric
open LpSelfSimilar.Geometry
open scoped ENNReal

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- Two points of an affine unit interval are at distance at most its scale. -/
theorem dist_le_scale_of_mem_interval (q : PositiveAffine) {x y : ℝ}
    (hx : x ∈ q.interval) (hy : y ∈ q.interval) : dist x y ≤ q.scale := by
  rcases hx with ⟨hx0, hx1⟩
  rcases hy with ⟨hy0, hy1⟩
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- Below threshold one, an interval contained in E passes the concentration test. -/
theorem isConcentrated_of_interval_subset {E : Set ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (q : PositiveAffine) (hsub : q.interval ⊆ E) :
    IsConcentrated E r q := by
  unfold IsConcentrated
  rw [inter_eq_right.mpr hsub, q.volume_interval, ← ENNReal.ofReal_mul hr]
  apply (ENNReal.ofReal_lt_ofReal_iff q.scale_pos).mpr
  nlinarith [q.scale_pos]

/-- A nonconcentrated interval contains a point outside E. -/
theorem exists_notMem_of_not_concentrated {E : Set ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (q : PositiveAffine) (hfail : ¬IsConcentrated E r q) :
    ∃ y ∈ q.interval, y ∉ E := by
  by_contra h
  push Not at h
  exact hfail (isConcentrated_of_interval_subset hr hr1 q h)

/-- Every point of E in a nonconcentrated terminal interval belongs to a geometric inner layer. -/
theorem mem_innerBoundaryLayer_of_stopped_not_concentrated {θ r : ℝ}
    (hθ : 0 < θ) (hr : 0 ≤ r) (hr1 : r < 1) (E : Set ℝ)
    (n : ℕ) (w : Word Bool n)
    (hfail : ¬IsConcentrated E r (stoppedMap hθ E r n PositiveAffine.identity w))
    {x : ℝ} (hx : x ∈ E)
    (hxI : x ∈ (stoppedMap hθ E r n PositiveAffine.identity w).interval) :
    x ∈ innerBoundaryLayer E (θ ^ n) := by
  let q := stoppedMap hθ E r n PositiveAffine.identity w
  obtain ⟨y, hyI, hy⟩ := exists_notMem_of_not_concentrated hr hr1 q hfail
  apply mem_innerBoundaryLayer_of_dist_le hx hy
  have hscale : q.scale = θ ^ n := by
    simpa only [q, PositiveAffine.identity, mul_one] using
      stoppedMap_scale_eq_of_not_concentrated hθ E r n PositiveAffine.identity w hfail
  exact (dist_le_scale_of_mem_interval q hxI hyI).trans hscale.le

/-- Conditional E-mass in a nonconcentrated terminal interval is bounded by its boundary-layer mass. -/
theorem stopped_preimage_mass_le_boundaryLayer_of_not_concentrated {θ r : ℝ}
    (hθ : 0 < θ) (hr : 0 ≤ r) (hr1 : r < 1) (μ : Measure ℝ)
    (hsupp : μ (Icc (0 : ℝ) 1)ᶜ = 0) (E : Set ℝ) (n : ℕ) (w : Word Bool n)
    (hfail : ¬IsConcentrated E r (stoppedMap hθ E r n PositiveAffine.identity w)) :
    μ ((stoppedMap hθ E r n PositiveAffine.identity w) ⁻¹' E) ≤
      μ ((stoppedMap hθ E r n PositiveAffine.identity w) ⁻¹' innerBoundaryLayer E (θ ^ n)) := by
  let q := stoppedMap hθ E r n PositiveAffine.identity w
  rw [← measure_inter_conull (s := q ⁻¹' E) hsupp]
  apply measure_mono
  rintro x ⟨hxE, hxI⟩
  apply mem_innerBoundaryLayer_of_stopped_not_concentrated hθ hr hr1 E n w hfail hxE
  change x ∈ q ⁻¹' q.interval
  rwa [q.preimage_interval]

end LpSelfSimilar.SelfSimilar.Concentration
