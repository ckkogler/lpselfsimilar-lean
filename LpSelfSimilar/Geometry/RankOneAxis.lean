module

public import LpSelfSimilar.Geometry.AxisProjection

@[expose] public section

/-!
# Normalizing the direction of a rank-one covariance defect

A nonzero defect vector determines a unit Euclidean axis. Its squared length
is exactly one minus the scalar noise variance. This converts the covariance
written with the unnormalized defect into the unit-axis covariance used by the
Gaussian decomposition. The nonzero assumption also covers empty-coordinate
degeneracies without an additional dimension assumption.
-/

open Matrix
open scoped InnerProductSpace

namespace LpSelfSimilar.Geometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An actual nonzero defect supplies a unit axis with the required covariance. -/
theorem exists_unit_axis_of_rankOneCovariance (w : ι → ℝ) (hw : w ≠ 0)
    (s : ℝ) (hs : 1 - w ⬝ᵥ w = s ^ 2) :
    ∃ e : EuclideanSpace ℝ ι, ‖e‖ = 1 ∧
      1 - vecMulVec w w =
        1 + (s ^ 2 - 1) • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) := by
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 w
  have hv : v ≠ 0 := by
    intro h
    apply hw
    exact congrArg WithLp.ofLp h
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let e : EuclideanSpace ℝ ι := ‖v‖⁻¹ • v
  have he : ‖e‖ = 1 := by
    simp only [e, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  have hdot : w ⬝ᵥ w = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, euclidean_real_inner_eq_dotProduct]
  have hout : vecMulVec w w =
      ‖v‖ ^ 2 • vecMulVec (WithLp.ofLp e) (WithLp.ofLp e) := by
    ext i j
    change w i * w j = ‖v‖ ^ 2 * ((‖v‖⁻¹ * w i) * (‖v‖⁻¹ * w j))
    field_simp
  have hcoeff : ‖v‖ ^ 2 = 1 - s ^ 2 := by rw [hdot] at hs; linarith
  refine ⟨e, he, ?_⟩
  rw [hout, hcoeff, sub_smul, one_smul, sub_smul, one_smul]
  abel

end LpSelfSimilar.Geometry
