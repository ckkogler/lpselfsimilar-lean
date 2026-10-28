module

public import LpSelfSimilar.SelfSimilar.Concentration.Definitions

@[expose] public section

/-!
# Parent failure bounds the conditional inverse-image volume

A child interval is contained in its parent and has theta times its length.
If the parent fails the concentration test at level r, the child's inverse
image of E inside [0,1] has volume at most r/theta. This is the geometric
step responsible for the exact conditional mass budget in sharp L2 stopping.
-/

open MeasureTheory Set
open LpSelfSimilar.Geometry
open scoped ENNReal

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- Every composed child interval is contained in its parent. -/
theorem child_interval_subset {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (q : PositiveAffine) (e : Bool) :
    (q.comp (digitMap hθ e)).interval ⊆ q.interval := by
  rw [← PositiveAffine.image_unitInterval, ← q.image_unitInterval]
  rintro _ ⟨x, hx, rfl⟩
  rw [PositiveAffine.comp_apply]
  refine ⟨digitMap hθ e x, ?_, rfl⟩
  apply digitMap_interval_subset hθ hθ1 e
  rw [← (digitMap hθ e).preimage_interval] at hx
  exact hx

/-- The child has theta times the parent's positive scale. -/
theorem child_scale {θ : ℝ} (hθ : 0 < θ) (q : PositiveAffine) (e : Bool) :
    (q.comp (digitMap hθ e)).scale = q.scale * θ := rfl

/-- Failure at the parent bounds the stopped child's inverse-image volume by r/theta. -/
theorem child_preimage_volume_le_of_parent_failure {θ r : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 ≤ r) (q : PositiveAffine) (e : Bool)
    (E : Set ℝ) (hfail : ¬IsConcentrated E r q) :
    volume ((q.comp (digitMap hθ e)) ⁻¹' E ∩ Icc 0 1) ≤ ENNReal.ofReal (r / θ) := by
  have hqs := q.scale_pos
  have hc := child_interval_subset hθ hθ1 q e
  have hf := (not_isConcentrated_iff E r q).mp hfail
  rw [PositiveAffine.volume_preimage_inter_unitInterval]
  calc
    _ ≤ ENNReal.ofReal ((q.comp (digitMap hθ e)).scale⁻¹) * volume (E ∩ q.interval) :=
      mul_le_mul' le_rfl (measure_mono (inter_subset_inter_right E hc))
    _ ≤ ENNReal.ofReal ((q.comp (digitMap hθ e)).scale⁻¹) *
        (ENNReal.ofReal r * volume q.interval) := mul_le_mul' le_rfl hf
    _ = ENNReal.ofReal (r / θ) := by
      rw [child_scale, q.volume_interval, ← ENNReal.ofReal_mul hr,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp [q.scale_pos.ne', hθ.ne']

/-- A parent failure gives conditional mass at most K*r/theta+e under the stated small-set bound. -/
theorem child_preimage_mass_le_of_parent_failure {θ r K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hr : 0 ≤ r) (hK : 0 ≤ K) (he : 0 ≤ e)
    (μ : Measure ℝ) (hsupp : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hbound : ∀ A : Set ℝ, MeasurableSet A →
      μ A ≤ ENNReal.ofReal K * volume A + ENNReal.ofReal e)
    (q : PositiveAffine) (b : Bool) {E : Set ℝ} (hE : MeasurableSet E)
    (hfail : ¬IsConcentrated E r q) :
    μ ((q.comp (digitMap hθ b)) ⁻¹' E) ≤ ENNReal.ofReal (K * (r / θ) + e) := by
  let c := q.comp (digitMap hθ b)
  rw [← measure_inter_conull (s := c ⁻¹' E) hsupp]
  have hA : MeasurableSet (c ⁻¹' E ∩ Icc 0 1) := (hE.preimage c.measurable).inter measurableSet_Icc
  have hv := child_preimage_volume_le_of_parent_failure hθ hθ1 hr q b E hfail
  calc
    _ ≤ ENNReal.ofReal K * volume (c ⁻¹' E ∩ Icc 0 1) + ENNReal.ofReal e := hbound _ hA
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal (r / θ) + ENNReal.ofReal e :=
      add_le_add (mul_le_mul' le_rfl hv) le_rfl
    _ = _ := by rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_add (by positivity) he]

/-- At the exact stopping level theta*e/K the conditional mass budget is twice e. -/
theorem child_preimage_mass_le_twice_error {θ K e : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hK : 0 < K) (he : 0 ≤ e)
    (μ : Measure ℝ) (hsupp : μ (Icc (0 : ℝ) 1)ᶜ = 0)
    (hbound : ∀ A : Set ℝ, MeasurableSet A →
      μ A ≤ ENNReal.ofReal K * volume A + ENNReal.ofReal e)
    (q : PositiveAffine) (b : Bool) {E : Set ℝ} (hE : MeasurableSet E)
    (hfail : ¬IsConcentrated E (θ * (e / K)) q) :
    μ ((q.comp (digitMap hθ b)) ⁻¹' E) ≤ ENNReal.ofReal (2 * e) := by
  have h := child_preimage_mass_le_of_parent_failure hθ hθ1 (by positivity) hK.le he μ
    hsupp hbound q b hE hfail
  convert! h using 1
  congr 1
  field_simp [hK.ne', hθ.ne']
  <;> ring

end LpSelfSimilar.SelfSimilar.Concentration
