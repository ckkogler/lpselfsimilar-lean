module

public import LpSelfSimilar.Geometry.Similarity

@[expose] public section

/-!
The inverse-image estimate on page 3, with an explicit diameter bound `D`.
The paper's normalization is recovered by setting `D = 1`.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LpSelfSimilar

/-- The geometric constant in (2.2), retaining the diameter bound `D`. -/
noncomputable def smallSetConstant (d : ℕ) (a D : ℝ) : ℝ :=
  (D / a) ^ d * volume.real (ball (0 : Space d) 1)

lemma smallSetConstant_pos {d : ℕ} {a D : ℝ} (ha : 0 < a) (hD : 0 < D) :
    0 < smallSetConstant d a D :=
  mul_pos (pow_pos (div_pos hD ha) _) (volume_real_ball_pos _ zero_lt_one)

/-- A stopped similarity has uniformly controlled inverse-image volume relative
to the testing ball. All divisions have strictly positive finite denominators. -/
lemma Similarity.volume_preimage_le {d : ℕ} (g : Similarity d)
    {a D r : ℝ} (ha : 0 < a) (hD : 0 < D) (hr : 0 < r)
    (hscale : a * (r / D) ≤ g.ratio) (x : Space d)
    {E : Set (Space d)} (hE : MeasurableSet E) :
    volume (g ⁻¹' E) ≤ ENNReal.ofReal (smallSetConstant d a D) *
      (volume E / volume (ball x r)) := by
  have hv := volume_real_ball_pos (0 : Space d) zero_lt_one
  have hinv : g.ratio⁻¹ ≤ D / (a * r) := by
    have hpos : 0 < a * (r / D) := mul_pos ha (div_pos hr hD)
    calc
      g.ratio⁻¹ ≤ (a * (r / D))⁻¹ := inv_anti₀ hpos hscale
      _ = D / (a * r) := by field_simp
  have hpow : (g.ratio ^ d)⁻¹ ≤ (D / a) ^ d / r ^ d := by
    rw [← inv_pow, ← div_pow]
    have heq : D / a / r = D / (a * r) := by field_simp
    rw [heq]
    exact pow_le_pow_left₀ (inv_nonneg.mpr g.ratio_pos.le) hinv d
  have hball : volume (ball x r) =
      ENNReal.ofReal (r ^ d * volume.real (ball (0 : Space d) 1)) := by
    rw [ENNReal.ofReal_mul (pow_pos hr d).le, volume_ball_formula x hr]
    rw [measureReal_def, ENNReal.ofReal_toReal measure_ball_ne_top]
  have hfactor : ENNReal.ofReal ((D / a) ^ d / r ^ d) =
      ENNReal.ofReal (smallSetConstant d a D) / volume (ball x r) := by
    rw [hball, ← ENNReal.ofReal_div_of_pos (mul_pos (pow_pos hr d) hv)]
    congr 1
    dsimp [smallSetConstant]
    field_simp
  rw [g.volume_preimage E hE]
  calc
    ENNReal.ofReal ((g.ratio ^ d)⁻¹) * volume E ≤
        ENNReal.ofReal ((D / a) ^ d / r ^ d) * volume E :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) le_rfl
    _ = ENNReal.ofReal (smallSetConstant d a D) * (volume E / volume (ball x r)) := by
      rw [hfactor, div_eq_mul_inv, div_eq_mul_inv]
      ac_rfl

end LpSelfSimilar
