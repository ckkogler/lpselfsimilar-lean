module

public import LpSelfSimilar.Analysis.MeasurePreservingDensity
public import LpSelfSimilar.Analysis.ConjugateDensity

@[expose] public section

/-!
Positive dilation preserves integrability exponents. The density of the mapped
measure is explicitly c⁻¹ f(c⁻¹ x), with its Jacobian justified by Lebesgue
measure's exact dilation formula.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace LpSelfSimilar

lemma map_density_mul_pos {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))).map (fun x ↦ c * x) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (c⁻¹ * f (c⁻¹ * x))) := by
  let e := MeasurableEquiv.mulLeft₀ c hc.ne'
  have hMP : MeasurePreserving e volume (ENNReal.ofReal c⁻¹ • volume) :=
    ⟨e.measurable, by simpa only [e, MeasurableEquiv.coe_mulLeft₀, abs_of_pos (inv_pos.mpr hc)]
      using Real.map_volume_mul_left hc.ne'⟩
  have h := map_withDensity_of_measurePreserving e hMP (fun x ↦ ENNReal.ofReal (f x))
  change (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))).map (fun x ↦ c * x) =
    (ENNReal.ofReal c⁻¹ • volume).withDensity
    (fun x ↦ ENNReal.ofReal (f (c⁻¹ * x))) at h
  rw [h, withDensity_smul_measure, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  exact (ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)).symm

lemma memLp_comp_mul_pos {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} {p : ℝ≥0∞}
    (hf : MemLp f p volume) : MemLp (fun x ↦ f (c * x)) p volume := by
  have hmap : MemLp f p (volume.map (fun x ↦ c * x)) := by
    rw [Real.map_volume_mul_left hc.ne']
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact hmap.comp_of_map (by fun_prop)

/-- Every positive scaled copy retains an actual density at the same exponent. -/
theorem exists_density_map_mul_pos {μ : Measure ℝ} {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : Integrable f volume) (hn : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {p : ℝ≥0∞} (hLp : MemLp f p volume) :
    ∃ F : ℝ → ℝ, (∀ x, 0 ≤ F x) ∧ Integrable F volume ∧
      μ.map (fun x ↦ c * x) = volume.withDensity (fun x ↦ ENNReal.ofReal (F x)) ∧
      MemLp F p volume := by
  refine ⟨fun x ↦ c⁻¹ * f (c⁻¹ * x), fun x ↦ mul_nonneg (inv_nonneg.mpr hc.le) (hn _),
    (hf.comp_mul_left' (inv_ne_zero hc.ne')).const_mul _, ?_, ?_⟩
  · rw [hμ, map_density_mul_pos hc]
  · exact (memLp_comp_mul_pos (inv_pos.mpr hc) hLp).const_mul _

end LpSelfSimilar
