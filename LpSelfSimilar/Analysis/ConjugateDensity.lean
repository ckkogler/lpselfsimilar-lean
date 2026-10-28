module

public import LpSelfSimilar.Analysis.YoungDensity
public import LpSelfSimilar.Analysis.LpConvolutionContinuity

@[expose] public section

/-!
An actual continuous density for the convolution of two measures with densities
at conjugate finite exponents. The integral formula is identified by Tonelli
and almost-everywhere existence of the Bochner convolution.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace LpSelfSimilar

lemma convolution_density_of_measurable {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hfm : Measurable f) (hgm : Measurable g)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    (volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) ∗
      (volume.withDensity (fun x ↦ ENNReal.ofReal (g x))) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (functionConvolution f g x)) := by
  have hfin : (∫⁻ x, ENNReal.ofReal (f x)) < ∞ := by
    simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal (hfn _)] using hf.hasFiniteIntegral
  rw [withDensity_convolution_measurable hfm.ennreal_ofReal hgm.ennreal_ofReal hfin]
  apply withDensity_congr_ae
  have hex := hf.ae_convolution_exists (ContinuousLinearMap.mul ℝ ℝ) hg
  filter_upwards [hex] with x hx
  have hi : Integrable (fun z ↦ f z * g (x - z)) volume := hx
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun z ↦ mul_nonneg (hfn z) (hgn (x - z))))
  change _ = ENNReal.ofReal (∫ z, f z * g (x - z))
  rw [he]
  apply lintegral_congr
  intro z
  exact (ENNReal.ofReal_mul (hfn z)).symm

/-- Choose a measurable nonnegative real density without changing its Lp class. -/
lemma exists_measurable_real_density {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : Integrable f volume) (hn : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    {p : ℝ} (hp : 0 < p) (hLp : MemLp f (ENNReal.ofReal p) volume) :
    ∃ F : ℝ → ℝ, Measurable F ∧ (∀ x, 0 ≤ F x) ∧ Integrable F volume ∧
      μ = volume.withDensity (fun x ↦ ENNReal.ofReal (F x)) ∧
      MemLp F (ENNReal.ofReal p) volume := by
  obtain ⟨G, hG, heq, hG1, hGp⟩ := exists_measurable_ennreal_density hf hn hp hLp
  refine ⟨fun x ↦ (G x).toReal, hG.ennreal_toReal, fun _ ↦ ENNReal.toReal_nonneg,
    integrable_ennreal_toReal hG hG1, ?_, memLp_ennreal_toReal hG hp hGp⟩
  rw [hμ]
  exact withDensity_congr_ae (heq.trans (ennreal_toReal_ae hG hG1).symm)

/-- Conjugate finite power densities yield a continuous nonnegative density. -/
theorem exists_continuous_density_convolution {μ ν : Measure ℝ} {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hν : ν = volume.withDensity (fun x ↦ ENNReal.ofReal (g x)))
    {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 1 / p + 1 / q = 1)
    (hfp : MemLp f (ENNReal.ofReal p) volume) (hgq : MemLp g (ENNReal.ofReal q) volume) :
    ∃ h : ℝ → ℝ, (∀ x, 0 ≤ h x) ∧ Continuous h ∧ Integrable h volume ∧
      μ ∗ ν = volume.withDensity (fun x ↦ ENNReal.ofReal (h x)) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  obtain ⟨F, hFm, hFn, hFi, hFrep, hFp⟩ := exists_measurable_real_density hf hfn hμ hp0 hfp
  obtain ⟨G, hGm, hGn, hGi, hGrep, hGq⟩ := exists_measurable_real_density hg hgn hν hq0 hgq
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp⟩
  haveI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by simpa using ENNReal.ofReal_le_ofReal hq⟩
  haveI : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) := by
    apply ENNReal.holderConjugate_iff.mpr
    rw [← ENNReal.ofReal_inv_of_pos hp0, ← ENNReal.ofReal_inv_of_pos hq0,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    simpa only [one_div, ENNReal.ofReal_one] using congrArg ENNReal.ofReal hs
  refine ⟨functionConvolution F G, ?_,
    continuous_functionConvolution_of_memLp ENNReal.ofReal_ne_top hFp hGq, ?_, ?_⟩
  · intro x
    exact integral_nonneg (fun z ↦ mul_nonneg (hFn z) (hGn (x - z)))
  · exact hFi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hGi
  · rw [hFrep, hGrep]
    exact convolution_density_of_measurable hFi hGi hFm hGm hFn hGn

end LpSelfSimilar
