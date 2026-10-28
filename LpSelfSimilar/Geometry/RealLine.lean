module

public import LpSelfSimilar.Geometry.Euclidean

@[expose] public section

/-!
The one-dimensional Euclidean space is the real line, with the same norm and
Lebesgue volume. This explicit bridge lets real Bernoulli convolutions reuse
the unchanged Euclidean statements of Lemma 2.1 and Theorem 1.1.
-/

open MeasureTheory Metric Set

namespace LpSelfSimilar

/-- Evaluation at the only coordinate, as a linear isometric equivalence. -/
noncomputable def realLine : Space 1 ≃ₗᵢ[ℝ] ℝ where
  toLinearEquiv := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).toLinearEquiv
  norm_map' x := by
    change ‖x 0‖ = ‖x‖
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs]

@[simp] lemma realLine_apply (x : Space 1) : realLine x = x 0 := rfl

lemma realLine_measurePreserving : MeasurePreserving realLine volume volume :=
  realLine.measurePreserving

lemma realLine_symm_measurePreserving : MeasurePreserving realLine.symm volume volume :=
  realLine.symm.measurePreserving

lemma volume_realLine_unitBall : volume.real (ball (0 : Space 1) 1) = 2 := by
  have h := realLine.measurePreserving.measure_preimage (s := ball (0 : ℝ) 1)
    isOpen_ball.measurableSet.nullMeasurableSet
  have he : realLine ⁻¹' ball (0 : ℝ) 1 = ball (0 : Space 1) 1 := by
    ext x
    simp only [mem_preimage, mem_ball, ← realLine.map_zero, realLine.dist_map]
  rw [he] at h
  have hr := congrArg ENNReal.toReal h
  simpa [measureReal_def, Real.volume_ball] using hr

end LpSelfSimilar
