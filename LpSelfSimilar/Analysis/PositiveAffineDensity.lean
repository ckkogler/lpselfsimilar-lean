module

public import LpSelfSimilar.Analysis.ScaledDensity
public import LpSelfSimilar.Geometry.PositiveAffine

@[expose] public section

/-!
# Density and Lp transport under positive affine maps

Translation and positive dilation give the exact Jacobian density for a real
positive affine map. The same transformations preserve each finite or infinite
Lp exponent, and their inverse composition transfers an Lp conclusion back to
the original density. All maps here are actual real functions.
-/

open MeasureTheory Set
open LpSelfSimilar.Geometry
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- Translation by b transports a density to x ↦ f(x-b). -/
theorem map_density_add_right (b : ℝ) (f : ℝ → ℝ) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).map (fun x => x + b) =
      volume.withDensity (fun x => ENNReal.ofReal (f (x - b))) := by
  let e := MeasurableEquiv.addRight b
  have h := map_withDensity_of_measurePreserving e
    (measurePreserving_add_right volume b) (fun x => ENNReal.ofReal (f x))
  simpa only [e, MeasurableEquiv.coe_addRight, MeasurableEquiv.symm_addRight, sub_eq_add_neg] using h

/-- The exact density formula for any positive affine real map. -/
theorem map_density_positiveAffine (q : PositiveAffine) (f : ℝ → ℝ) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).map q =
      volume.withDensity (fun x => ENNReal.ofReal
        (q.scale⁻¹ * f (q.scale⁻¹ * (x - q.shift)))) := by
  have heq : (fun x : ℝ => q.scale * x + q.shift) =
      (fun x : ℝ => x + q.shift) ∘ (fun x : ℝ => q.scale * x) := rfl
  change (volume.withDensity (fun x => ENNReal.ofReal (f x))).map
    (fun x => q.scale * x + q.shift) = _
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop), map_density_mul_pos q.scale_pos,
    map_density_add_right]

/-- Composition with a translation preserves every Lp exponent. -/
theorem memLp_comp_add_right {f : ℝ → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (b : ℝ) : MemLp (fun x => f (x + b)) p volume :=
  hf.comp_measurePreserving (measurePreserving_add_right volume b)

/-- Composition with a positive affine map preserves every Lp exponent. -/
theorem memLp_comp_positiveAffine {f : ℝ → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) (q : PositiveAffine) : MemLp (fun x => f (q x)) p volume := by
  exact memLp_comp_mul_pos q.scale_pos (memLp_comp_add_right hf q.shift)

/-- An Lp bound for the transported Jacobian density transfers back to the original density. -/
theorem memLp_of_positiveAffine_density {f : ℝ → ℝ} {p : ℝ≥0∞} (q : PositiveAffine)
    (hf : MemLp (fun x => q.scale⁻¹ * f (q.scale⁻¹ * (x - q.shift))) p volume) :
    MemLp f p volume := by
  have h := (memLp_comp_positiveAffine hf q).const_mul q.scale
  convert h using 1
  funext x
  change f x = q.scale * (q.scale⁻¹ * f (q.scale⁻¹ * (q.scale * x + q.shift - q.shift)))
  simp [q.scale_pos.ne']

end LpSelfSimilar.Analysis
