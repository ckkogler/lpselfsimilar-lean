module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic

@[expose] public section

/-!
# A squared-energy majorant for a cutoff times a Fourier amplitude

The two summands in the differentiated product are squared with an exact
factor two. Integrable squared cutoff and slope majorants then give both
integrability and the weighted energy bound on any measurable frequency set.
This is independent of the arithmetic or probabilistic source of the amplitude.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Analysis

/-- The product and its formal first-derivative expression have the stated pointwise energy bound. -/
theorem sq_cutoff_product_energy_le {q d E C : ℝ} {z w : ℂ}
    (hq : 0 ≤ q) (hz : ‖z‖ ≤ E) (hw : ‖w‖ ≤ C * E) :
    ‖(q : ℂ) * z‖ ^ 2 + ‖(d : ℂ) * z + (q : ℂ) * w‖ ^ 2 ≤
      E ^ 2 * ((1 + 2 * C ^ 2) * q ^ 2 + 2 * d ^ 2) := by
  have hqz : ‖(q : ℂ) * z‖ ≤ q * E := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
    exact mul_le_mul_of_nonneg_left hz hq
  have hdz : ‖(d : ℂ) * z‖ ≤ |d| * E := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg d)
  have hqw : ‖(q : ℂ) * w‖ ≤ q * (C * E) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
    exact mul_le_mul_of_nonneg_left hw hq
  have hsum := pow_le_pow_left₀ (norm_nonneg ((d : ℂ) * z + (q : ℂ) * w))
    (norm_add_le ((d : ℂ) * z) ((q : ℂ) * w)) 2
  have htwo : ‖(d : ℂ) * z + (q : ℂ) * w‖ ^ 2 ≤
      2 * ‖(d : ℂ) * z‖ ^ 2 + 2 * ‖(q : ℂ) * w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖(d : ℂ) * z‖ - ‖(q : ℂ) * w‖)]
  have h0 := pow_le_pow_left₀ (norm_nonneg _) hqz 2
  have h1 := pow_le_pow_left₀ (norm_nonneg _) hdz 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hqw 2
  calc
    _ ≤ (q * E) ^ 2 + 2 * (|d| * E) ^ 2 + 2 * (q * (C * E)) ^ 2 := by nlinarith
    _ = _ := by rw [mul_pow |d| E, sq_abs]; ring

/-- An integrable square majorant supplies the product energy's restricted integrability. -/
theorem integrableOn_cutoff_product_energy {E C : ℝ} {s : Set ℝ}
    {q d : ℝ → ℝ} {P R : ℝ → ℂ} (hs : MeasurableSet s)
    (hq : AEStronglyMeasurable q (volume.restrict s))
    (hd : AEStronglyMeasurable d (volume.restrict s))
    (hP : AEStronglyMeasurable P (volume.restrict s))
    (hR : AEStronglyMeasurable R (volume.restrict s))
    (hiq : Integrable (fun u => q u ^ 2)) (hid : Integrable (fun u => d u ^ 2))
    (hq0 : ∀ u ∈ s, 0 ≤ q u) (h0 : ∀ u ∈ s, ‖P u‖ ≤ E)
    (h1 : ∀ u ∈ s, ‖R u‖ ≤ C * E) :
    IntegrableOn (fun u => ‖(q u : ℂ) * P u‖ ^ 2 +
      ‖(d u : ℂ) * P u + (q u : ℂ) * R u‖ ^ 2) s := by
  have hqc : AEStronglyMeasurable (fun u => (q u : ℂ)) (volume.restrict s) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hq
  have hdc : AEStronglyMeasurable (fun u => (d u : ℂ)) (volume.restrict s) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hd
  have hm : Integrable (fun u : ℝ => E ^ 2 * ((1 + 2 * C ^ 2) * q u ^ 2 + 2 * d u ^ 2)) :=
    ((hiq.const_mul (1 + 2 * C ^ 2)).add (hid.const_mul 2)).const_mul (E ^ 2)
  refine hm.integrableOn.mono'
    (((hqc.mul hP).norm.pow 2).add (((hdc.mul hP).add (hqc.mul hR)).norm.pow 2)) ?_
  apply (ae_restrict_iff' hs).2
  exact ae_of_all _ (fun u hu => by
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact sq_cutoff_product_energy_le (hq0 u hu) (h0 u hu) (h1 u hu))

/-- The exact weighted product-energy estimate in terms of the two whole-line cutoff energies. -/
theorem half_integral_cutoff_product_energy_le {E C : ℝ} {s : Set ℝ}
    {q d : ℝ → ℝ} {P R : ℝ → ℂ} (hs : MeasurableSet s)
    (hq : AEStronglyMeasurable q (volume.restrict s))
    (hd : AEStronglyMeasurable d (volume.restrict s))
    (hP : AEStronglyMeasurable P (volume.restrict s))
    (hR : AEStronglyMeasurable R (volume.restrict s))
    (hiq : Integrable (fun u => q u ^ 2)) (hid : Integrable (fun u => d u ^ 2))
    (hq0 : ∀ u ∈ s, 0 ≤ q u) (h0 : ∀ u ∈ s, ‖P u‖ ≤ E)
    (h1 : ∀ u ∈ s, ‖R u‖ ≤ C * E) :
    (1 / 2 : ℝ) * (∫ u in s, ‖(q u : ℂ) * P u‖ ^ 2 +
      ‖(d u : ℂ) * P u + (q u : ℂ) * R u‖ ^ 2) ≤
      E ^ 2 * ((1 / 2 : ℝ) * (1 + 2 * C ^ 2) * (∫ u : ℝ, q u ^ 2) +
        ∫ u : ℝ, d u ^ 2) := by
  have hi := integrableOn_cutoff_product_energy hs hq hd hP hR hiq hid hq0 h0 h1
  have hm : Integrable (fun u : ℝ => E ^ 2 * ((1 + 2 * C ^ 2) * q u ^ 2 + 2 * d u ^ 2)) :=
    ((hiq.const_mul (1 + 2 * C ^ 2)).add (hid.const_mul 2)).const_mul (E ^ 2)
  have hl := setIntegral_mono_on hi hm.integrableOn hs
    (fun u hu => sq_cutoff_product_energy_le (hq0 u hu) (h0 u hu) (h1 u hu))
  have hg := setIntegral_le_integral (s := s) hm (ae_of_all _ (fun u => by positivity))
  have hb := mul_le_mul_of_nonneg_left (hl.trans hg) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  refine hb.trans_eq ?_
  rw [integral_const_mul, integral_add (hiq.const_mul _) (hid.const_mul _),
    integral_const_mul, integral_const_mul]
  ring

end LpSelfSimilar.Analysis
