module

public import LpSelfSimilar.Geometry.Euclidean
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.Action

@[expose] public section

/-!
Euclidean similarities, written exactly as in the paper: `x ↦ ρ • U x + b`,
where `ρ > 0` and `U` is an orthogonal linear equivalence. Contraction is a
separate condition, so finite compositions and the identity use the same type.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

noncomputable section

/-- A Euclidean similarity with positive ratio; reflections are allowed. -/
structure Similarity (d : ℕ) where
  ratio : ℝ
  ratio_pos : 0 < ratio
  orthogonal : Space d ≃ₗᵢ[ℝ] Space d
  shift : Space d

namespace Similarity

variable {d : ℕ}

instance : CoeFun (Similarity d) (fun _ ↦ Space d → Space d) :=
  ⟨fun g x ↦ g.ratio • g.orthogonal x + g.shift⟩

@[simp] lemma apply_def (g : Similarity d) (x : Space d) :
    g x = g.ratio • g.orthogonal x + g.shift := rfl

def identity (d : ℕ) : Similarity d where
  ratio := 1
  ratio_pos := zero_lt_one
  orthogonal := LinearIsometryEquiv.refl ℝ (Space d)
  shift := 0

@[simp] lemma identity_apply (x : Space d) : identity d x = x := by simp [identity]
@[simp] lemma identity_ratio : (identity d).ratio = 1 := rfl

/-- Composition is in the order `g ∘ h`, as for the stopped products in the paper. -/
def comp (g h : Similarity d) : Similarity d where
  ratio := g.ratio * h.ratio
  ratio_pos := mul_pos g.ratio_pos h.ratio_pos
  orthogonal := h.orthogonal.trans g.orthogonal
  shift := g.ratio • g.orthogonal h.shift + g.shift

@[simp] lemma comp_ratio (g h : Similarity d) : (g.comp h).ratio = g.ratio * h.ratio := rfl

@[simp] lemma comp_apply (g h : Similarity d) (x : Space d) : (g.comp h) x = g (h x) := by
  simp [comp, smul_add, smul_smul, add_assoc]

lemma continuous (g : Similarity d) : Continuous g :=
  (g.orthogonal.continuous.const_smul g.ratio).add continuous_const

lemma measurable (g : Similarity d) : Measurable g := g.continuous.measurable

lemma dist_eq (g : Similarity d) (x y : Space d) :
    dist (g x) (g y) = g.ratio * dist x y := by
  simp [dist_smul₀, Real.norm_eq_abs, abs_of_pos g.ratio_pos]

lemma norm_apply_le (g : Similarity d) (x : Space d) :
    ‖g x‖ ≤ g.ratio * ‖x‖ + ‖g.shift‖ := by
  calc
    ‖g x‖ ≤ ‖g.ratio • g.orthogonal x‖ + ‖g.shift‖ := norm_add_le _ _
    _ = _ := by simp [norm_smul, abs_of_pos g.ratio_pos]

/-- Inverse images scale Lebesgue volume by the inverse `d`th power of the ratio. -/
lemma volume_preimage (g : Similarity d) (E : Set (Space d)) (hE : MeasurableSet E) :
    volume (g ⁻¹' E) = ENNReal.ofReal ((g.ratio ^ d)⁻¹) * volume E := by
  have htrans : volume ((fun x : Space d ↦ x + g.shift) ⁻¹' E) = volume E :=
    (measurePreserving_add_right volume g.shift).measure_preimage hE.nullMeasurableSet
  have horth := g.orthogonal.measurePreserving.measure_preimage
    (s := (fun x : Space d ↦ g.ratio • x + g.shift) ⁻¹' E)
    (hE.preimage ((continuous_id.const_smul g.ratio).add
      continuous_const).measurable).nullMeasurableSet
  change volume (g.orthogonal ⁻¹' ((fun x : Space d ↦ g.ratio • x + g.shift) ⁻¹' E)) = _
  rw [horth]
  change volume ((fun x : Space d ↦ g.ratio • x) ⁻¹'
    ((fun x : Space d ↦ x + g.shift) ⁻¹' E)) = _
  rw [Measure.addHaar_preimage_smul volume g.ratio_pos.ne', htrans]
  simp [Space, abs_of_pos (inv_pos.mpr (pow_pos g.ratio_pos d))]

end Similarity
end
end LpSelfSimilar
