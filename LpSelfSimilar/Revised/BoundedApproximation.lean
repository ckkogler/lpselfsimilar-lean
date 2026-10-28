module

public import LpSelfSimilar.Bernoulli.QuantitativeGain
public import LpSelfSimilar.Bernoulli.IntegrabilityExponent
public import LpSelfSimilar.Analysis.SupportedDensity

/-!
# Higher integrability of the supplied Bernoulli density

Lemma 3.3 of Kittle–Kogler follows from the proved quantitative self-similar
criterion. Density uniqueness transfers its conclusion to any supplied
nonnegative representing density. The bounded approximation is only required
to obey its height bound almost everywhere.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Revised

/-- Lemma 3.3, with the conclusion for the supplied density and an almost-
everywhere height bound for the approximation. Integrability of the error and
the approximation is equivalent once the density is integrable. -/
theorem density_memLp_of_bounded_approximation {l : ℝ}
    (hl0 : 1 / 2 < l) (hl1 : l < 1) {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    (hrep : Bernoulli.convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hg : Integrable g volume) (hbound : ∀ᵐ x ∂volume, g x ≤ 1 / 2)
    (herr : (∫ x, |f x - g x|) ≤ 1 / (2 * 21 ^ 2)) :
    MemLp f (ENNReal.ofReal (1 + 1 / (10 * (1 - Real.log (1 - l))))) volume := by
  let g' : ℝ → ℝ := fun x ↦ min (g x) (1 / 2)
  have hgg' : g' =ᵐ[volume] g := by
    filter_upwards [hbound] with x hx
    exact min_eq_left hx
  have hg' : Integrable g' volume := hg.congr hgg'.symm
  have herr' : (∫ x, |f x - g' x|) ≤ 1 / (2 * 21 ^ 2) := by
    calc
      (∫ x, |f x - g' x|) = ∫ x, |f x - g x| := by
        apply integral_congr_ae
        filter_upwards [hgg'] with x hx
        rw [hx]
      _ ≤ 1 / (2 * 21 ^ 2) := herr
  obtain ⟨F, hF0, hF, hFrep, hFp⟩ :=
    Bernoulli.higher_integrability_of_bounded_approximation hl0.le hl1 hf hf0 hrep
      hg' (fun x ↦ min_le_right _ _) herr'
  obtain ⟨G, hG0, hG, hGrep, hGp, _⟩ := exists_supported_density_memLp hF hF0 hFrep
    measurableSet_Icc (Bernoulli.convolution_compl_interval l (by linarith) hl1)
    (by simp [Real.volume_Icc]) hFp
    (ENNReal.ofReal_le_ofReal (Bernoulli.integrabilityGain_le_exact hl0.le hl1))
  have hsame : G =ᵐ[volume] f :=
    (density_ae_eq_of_representation hG hG0 hGrep).symm.trans
      (density_ae_eq_of_representation hf hf0 hrep)
  have h := (memLp_congr_ae hsame).mp hGp
  simpa only [Bernoulli.integrabilityGain, Real.log_inv, sub_eq_add_neg] using h

/-- The norm formulation of Lemma 3.3. The finite `L¹` error supplies the
integrability of the approximation; its `L∞` bound is interpreted essentially. -/
theorem density_memLp_of_L1_Linfty_approximation {l : ℝ}
    (hl0 : 1 / 2 < l) (hl1 : l < 1) {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    (hrep : Bernoulli.convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hbound : eLpNorm g ∞ volume ≤ ENNReal.ofReal (1 / 2 : ℝ))
    (herr : eLpNorm (fun x ↦ f x - g x) 1 volume ≤
      ENNReal.ofReal (1 / (2 * 21 ^ 2) : ℝ)) :
    MemLp f (ENNReal.ofReal (1 + 1 / (10 * (1 - Real.log (1 - l))))) volume := by
  have hdiffLp : MemLp (fun x ↦ f x - g x) 1 volume :=
    memLp_iff.mpr (herr.trans_lt ENNReal.ofReal_lt_top)
  have hdiff := memLp_one_iff_integrable.mp hdiffLp
  have hg : Integrable g volume := by
    convert hf.sub hdiff using 1
    funext x
    dsimp
    ring
  have hboundAE : ∀ᵐ x ∂volume, g x ≤ 1 / 2 := by
    filter_upwards [enorm_ae_le_eLpNormEssSup g volume] with x hx
    have hh := hx.trans (eLpNormEssSup_le_eLpNorm_top.trans hbound)
    rw [Real.enorm_eq_ofReal_abs] at hh
    exact (le_abs_self _).trans ((ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp hh)
  have herrIntegral : (∫ x, |f x - g x|) ≤ 1 / (2 * 21 ^ 2) := by
    have heq : ENNReal.ofReal (∫ x, |f x - g x|) =
        eLpNorm (fun x ↦ f x - g x) 1 volume := by
      rw [eLpNorm_one_eq_lintegral_enorm hdiff.aestronglyMeasurable]
      simpa only [Real.norm_eq_abs] using ofReal_integral_norm_eq_lintegral_enorm hdiff
    rw [← heq] at herr
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp herr
  exact density_memLp_of_bounded_approximation hl0 hl1 hf hf0 hrep hg hboundAE herrIntegral

end LpSelfSimilar.Revised
