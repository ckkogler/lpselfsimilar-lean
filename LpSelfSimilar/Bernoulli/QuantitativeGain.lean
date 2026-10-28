module

public import LpSelfSimilar.Bernoulli.HigherIntegrability
public import LpSelfSimilar.Bernoulli.EuclideanSupport
public import LpSelfSimilar.Bernoulli.GainExponent
public import LpSelfSimilar.Analysis.BoundedApproximationMass
public import LpSelfSimilar.Analysis.SmallSetMassTransport
public import LpSelfSimilar.Analysis.DensityUniqueness
public import LpSelfSimilar.SelfSimilar.QuantitativeCriterion

@[expose] public section

/-!
Bounded approximation gives quantitative higher integrability. Theorem 1.1
supplies a representing Lp density for the actual Bernoulli system; the explicit
mass modulus, stopped-word (2.2) and exact Lemma 2.1 improve its exponent to the
quantitative value needed for the final convolution argument.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Bernoulli

/-- The quantitative self-similar step in Proposition 3.1, with the exact
Lemma 2.1 exponent. The approximation input is proved for rational parameters. -/
theorem higher_integrability_of_bounded_approximation {l : ℝ}
    (hl0 : 1 / 2 ≤ l) (hl1 : l < 1) {f f₀ : ℝ → ℝ}
    (hf : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    (hrep : convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hf₀ : Integrable f₀ volume) (hbound : ∀ x, f₀ x ≤ 1 / 2)
    (herr : (∫ x, |f x - f₀ x|) ≤ 1 / (2 * 21 ^ 2)) :
    ∃ g : ℝ → ℝ, (∀ x, 0 ≤ g x) ∧ Integrable g volume ∧
      convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (g x)) ∧
      MemLp g (ENNReal.ofReal (gainExponent l)) volume := by
  have hl : 0 < l := by linarith
  have hg : 0 < 1 - l := by linarith
  have hac : convolution l ≪ volume := by rw [hrep]; exact withDensity_absolutelyContinuous _ _
  obtain ⟨g, hg0, hgi, hgrep, _⟩ := higher_integrability_of_absolutelyContinuous hl hl1 hac
  have hmass : smallSetMass (convolution l) volume (ENNReal.ofReal (1 / 21 ^ 2 : ℝ)) ≤
      ENNReal.ofReal (1 / 21 ^ 2 : ℝ) := by
    have h := smallSetMass_le_of_bounded_density_approximation hf hf0 hrep hf₀
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hbound herr (by norm_num : (0 : ℝ) ≤ 1 / 21 ^ 2)
    norm_num at h ⊢
    exact h
  have hmassS : smallSetMass (euclideanLaw l) volume (ENNReal.ofReal (1 / 21 ^ 2 : ℝ)) ≤
      ENNReal.ofReal (1 / 21 ^ 2 : ℝ) :=
    smallSetMass_map_le realLine.symm.toHomeomorph.toMeasurableEquiv
      realLine_symm_measurePreserving (convolution l) hmass
  have hCε : smallSetConstant 1 l (2 / (1 - l)) * gainVolumeFraction l = 1 / 21 ^ 2 := by
    rw [bernoulli_smallSetConstant, gainVolumeFraction]
    field_simp
  have hD : (1 : ℝ) ≤ 2 / (1 - l) := by
    apply (le_div_iff₀ hg).mpr
    linarith
  have hsmall := (selfSimilarSystem hl hl1).small_set_hypothesis_of_mass_bound
    (euclideanLaw_stationary hl hl1) (euclideanSupport_compl_null hl.le hl1)
    (euclideanSupport_mass hl.le hl1) hl hl1 (fun _ ↦ le_rfl) hD
    (fun _ hx _ hy ↦ euclideanSupport_diameter hx hy)
    (show smallSetMass (euclideanLaw l) volume
        (ENNReal.ofReal (smallSetConstant 1 l (2 / (1 - l)) * gainVolumeFraction l)) ≤
          ENNReal.ofReal (1 / 21 ^ 2 : ℝ) from by rwa [hCε])
  have hLp := (weak_reverse_holder_measure (by norm_num : 1 ≤ 1)
    (euclideanLaw_absolutelyContinuous hac) (gainVolumeFraction_mem hl hl1)
    (by norm_num [coveringConstant] : (1 / 21 ^ 2 : ℝ) ∈ Ioo 0 (coveringConstant 1)⁻¹)
    hsmall).2
  have hgS : Integrable (g ∘ realLine) volume :=
    realLine_measurePreserving.integrable_comp_of_integrable hgi
  have hrepS : euclideanLaw l = volume.withDensity (fun x ↦ ENNReal.ofReal (g (realLine x))) := by
    rw [euclideanLaw, hgrep]
    exact map_withDensity_of_measurePreserving realLine.symm.toHomeomorph.toMeasurableEquiv
      realLine_symm_measurePreserving _
  have heq := density_ae_eq_of_representation hgS (fun x ↦ hg0 _) hrepS
  have hLpS := (memLp_congr_ae heq).mp hLp
  refine ⟨g, hg0, hgi, hgrep, ?_⟩
  have h := hLpS.comp_measurePreserving realLine_symm_measurePreserving
  simpa only [Function.comp_def, realLine.apply_symm_apply, gainExponent] using h

end LpSelfSimilar.Bernoulli
