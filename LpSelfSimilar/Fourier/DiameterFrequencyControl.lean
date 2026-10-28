module

public import LpSelfSimilar.Fourier.FiniteFrequencyControl
public import LpSelfSimilar.Geometry.FiniteDiameterTranslation

@[expose] public section

/-!
# Fourier norm control from diameter alone

Translate the nonzero atoms to put their support in `[0,D]`, apply the bounded
support estimate, and remove the translation using invariance of the Fourier
norm. This avoids adding an absolute-location hypothesis to conditional laws.
-/

open scoped BigOperators

namespace LpSelfSimilar.Fourier

/-- A diameter bound suffices to control variation of the Fourier norm. -/
theorem abs_norm_finiteTransform_sub_norm_le_of_diameter {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {D : ℝ} (hdiam : ∀ i, p i ≠ 0 → ∀ j, p j ≠ 0 → |z i - z j| ≤ D) (s t : ℝ) :
    |‖finiteTransform p z s‖ - ‖finiteTransform p z t‖| ≤ D * |s - t| := by
  obtain ⟨b, hb⟩ := Geometry.exists_translation_of_nonzero_diameter p z hdiam
  have hbound : ∀ i, p i ≠ 0 → |z i + (-b)| ≤ D := by
    intro i hi
    rw [← sub_eq_add_neg, abs_of_nonneg (hb i hi).1]
    exact (hb i hi).2
  have h := abs_norm_finiteTransform_sub_norm_le p (fun i ↦ z i + (-b)) hp hsum hbound s t
  simpa only [norm_finiteTransform_translate] using h

/-- A conditional law of diameter `52*r` loses at most `52*epsilon` on the frequency band. -/
theorem norm_finiteTransform_frequency_band_le_of_diameter {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {r ξ ε : ℝ} (hr : 0 < r)
    (hdiam : ∀ i, p i ≠ 0 → ∀ j, p j ≠ 0 → |z i - z j| ≤ 52 * r)
    (hξ : abs (|ξ| - 1) ≤ ε) :
    ‖finiteTransform p z (ξ / r)‖ ≤ ‖finiteTransform p z (1 / r)‖ + 52 * ε := by
  obtain ⟨b, hb⟩ := Geometry.exists_translation_of_nonzero_diameter p z hdiam
  have hbound : ∀ i, p i ≠ 0 → |z i + (-b)| ≤ 52 * r := by
    intro i hi
    rw [← sub_eq_add_neg, abs_of_nonneg (hb i hi).1]
    exact (hb i hi).2
  have h := norm_finiteTransform_frequency_band_le p (fun i ↦ z i + (-b)) hp hsum hr hbound hξ
  simpa only [norm_finiteTransform_translate] using h

end LpSelfSimilar.Fourier
