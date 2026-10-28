module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Tactic

@[expose] public section

/-!
# Positive affine maps and their unit-interval images

An orientation-preserving real similarity is recorded by its positive scale
and translation. Its actual action, composition, image interval, and Lebesgue
Jacobian are explicit. This real-line geometry supports concentration stopping
without imposing separation on the interval images.
-/

open MeasureTheory Set Metric
open scoped ENNReal

namespace LpSelfSimilar.Geometry

/-- A positive real affine similarity. -/
structure PositiveAffine where
  scale : ℝ
  shift : ℝ
  scale_pos : 0 < scale

namespace PositiveAffine

instance : CoeFun PositiveAffine (fun _ => ℝ → ℝ) := ⟨fun q x => q.scale * x + q.shift⟩

/-- The identity affine similarity. -/
def identity : PositiveAffine := ⟨1, 0, zero_lt_one⟩

/-- Composition of positive affine similarities. -/
def comp (q p : PositiveAffine) : PositiveAffine :=
  ⟨q.scale * p.scale, q.scale * p.shift + q.shift, mul_pos q.scale_pos p.scale_pos⟩

/-- Composition acts by ordinary function composition. -/
theorem comp_apply (q p : PositiveAffine) (x : ℝ) : q.comp p x = q (p x) := by
  change (q.scale * p.scale) * x + (q.scale * p.shift + q.shift) =
    q.scale * (p.scale * x + p.shift) + q.shift
  ring

/-- Every positive affine similarity is continuous. -/
theorem continuous (q : PositiveAffine) : Continuous q := by
  change Continuous (fun x : ℝ => q.scale * x + q.shift)
  fun_prop

/-- Every positive affine similarity is measurable. -/
theorem measurable (q : PositiveAffine) : Measurable q := q.continuous.measurable

/-- Its closed image of the unit interval. -/
def interval (q : PositiveAffine) : Set ℝ := Icc q.shift (q.scale + q.shift)

/-- Membership in the image interval is exactly membership in the unit interval before mapping. -/
theorem preimage_interval (q : PositiveAffine) : q ⁻¹' q.interval = Icc 0 1 := by
  ext x
  change (q.shift ≤ q.scale * x + q.shift ∧ q.scale * x + q.shift ≤ q.scale + q.shift) ↔
    (0 ≤ x ∧ x ≤ 1)
  constructor
  · rintro ⟨h0, h1⟩
    constructor <;> nlinarith [q.scale_pos]
  · rintro ⟨h0, h1⟩
    constructor <;> nlinarith [q.scale_pos]

/-- The actual affine image of [0,1] is the displayed interval. -/
theorem image_unitInterval (q : PositiveAffine) : q '' Icc 0 1 = q.interval := by
  apply subset_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (show x ∈ q ⁻¹' q.interval from by rwa [q.preimage_interval])
  · intro y hy
    let x := (y - q.shift) / q.scale
    have he : q x = y := by
      change q.scale * ((y - q.shift) / q.scale) + q.shift = y
      field_simp [q.scale_pos.ne']
      <;> ring
    refine ⟨x, ?_, he⟩
    rw [← q.preimage_interval]
    change q x ∈ q.interval
    rwa [he]

/-- The interval is a closed ball with half the scale as radius. -/
theorem interval_eq_closedBall (q : PositiveAffine) :
    q.interval = closedBall (q.shift + q.scale / 2) (q.scale / 2) := by
  rw [Real.closedBall_eq_Icc]
  congr 1 <;> dsimp only [interval] <;> congr 1 <;> ring

/-- The interval has Lebesgue volume equal to the positive scale. -/
theorem volume_interval (q : PositiveAffine) :
    volume q.interval = ENNReal.ofReal q.scale := by
  rw [interval, Real.volume_Icc]
  congr 1
  ring

/-- The full inverse image has the exact reciprocal-scale Lebesgue Jacobian. -/
theorem volume_preimage (q : PositiveAffine) (E : Set ℝ) :
    volume (q ⁻¹' E) = ENNReal.ofReal (q.scale⁻¹) * volume E := by
  have he : q ⁻¹' E = (fun x : ℝ => q.scale * x) ⁻¹' ((fun x : ℝ => x + q.shift) ⁻¹' E) := rfl
  rw [he, Real.volume_preimage_mul_left q.scale_pos.ne',
    measure_preimage_add_right, abs_of_pos (inv_pos.mpr q.scale_pos)]

/-- Restricting the inverse image to [0,1] is exactly restricting E to the image interval. -/
theorem volume_preimage_inter_unitInterval (q : PositiveAffine) (E : Set ℝ) :
    volume (q ⁻¹' E ∩ Icc 0 1) = ENNReal.ofReal (q.scale⁻¹) * volume (E ∩ q.interval) := by
  rw [← q.preimage_interval, ← preimage_inter, q.volume_preimage]

end PositiveAffine
end LpSelfSimilar.Geometry
