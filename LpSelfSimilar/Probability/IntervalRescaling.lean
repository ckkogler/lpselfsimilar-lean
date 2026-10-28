module

public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Tactic

@[expose] public section

/-!
# Rescaling a translated full-mass interval

Positive real rescaling takes a translated interval of length `D*r` to `[0,D]`.
This is an equality of actual mapped measures on the intervals, independent of
any probability normalization or finite-support representation.
-/

open MeasureTheory

namespace LpSelfSimilar

/-- Translation followed by positive rescaling has the exact interval preimage. -/
theorem map_sub_div_Icc (μ : Measure ℝ) (b D : ℝ) {r : ℝ} (hr : 0 < r) :
    (μ.map (fun x ↦ (x - b) / r)) (Set.Icc 0 D) =
      (μ.map (fun x ↦ x - b)) (Set.Icc 0 (D * r)) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc,
    Measure.map_apply (by fun_prop) measurableSet_Icc]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Icc, le_div_iff₀ hr, div_le_iff₀ hr, zero_mul]

end LpSelfSimilar
