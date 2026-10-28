module

public import LpSelfSimilar.Fourier.JointGeometricCancellation
public import LpSelfSimilar.Fourier.ConditionalFrequencyControl
public import LpSelfSimilar.Fourier.ScaledBandShift

@[expose] public section

/-!
# A shifted band block with support and frequency control

The exact first shift supplies the angular phase interval. The common extra
shift is fixed before the conditional label is sampled. Every resulting
conditional support has diameter below `52*r`, and can be translated into
`[0,52*r]`; on the entire two-sided frequency band the loss is `52*epsilon`.
This is the single-block input to independent digit packing.
-/

open scoped BigOperators
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Fourier

/-- Further geometric shifts keep every allowed conditional support within the diameter bound. -/
theorem scaled_band_cover_diameter_le {ι κ : Type*}
    (z : ι → ℝ) (cover : κ → Finset ι)
    {θ a r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 70)
    (ha : 0 < a) (hr : 0 < r) (k : ℕ)
    (hband : ∀ j i, i ∈ cover j → ∀ l, l ∈ cover j → i ≠ l → |z i - z l| < 16 * a) :
    ∀ j i, i ∈ cover j → ∀ l, l ∈ cover j →
      |θ ^ (bandFirstShift θ a r + (k : ℤ)) * z i -
        θ ^ (bandFirstShift θ a r + (k : ℤ)) * z l| ≤ 52 * r := by
  intro j i hi l hl
  by_cases hil : i = l
  · subst l
    simp only [sub_self, abs_zero]
    positivity
  have hc : 0 < θ ^ (bandFirstShift θ a r + (k : ℤ)) := zpow_pos hθ0 _
  rw [← mul_sub, abs_mul, abs_of_pos hc]
  exact ((mul_lt_mul_of_pos_left (hband j i hi l hl hil) hc).trans
    (shifted_band_width_lt hθ0 hθ1 hgap ha hr k)).le

/-- Shifting atom locations agrees exactly with the base-frequency parameterization. -/
theorem jointExpectedTransformNorm_shift {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → κ → ℝ) (z : ι → ℝ) {θ : ℝ} (hθ : θ ≠ 0) (m : ℤ) (k : ℕ) (r : ℝ) :
    jointExpectedTransformNorm u (fun i ↦ θ ^ (m + (k : ℤ)) * z i) (1 / r) =
      jointExpectedTransformNorm u z ((θ ^ m / r) * θ ^ k) := by
  have he : (1 / r) * θ ^ (m + (k : ℤ)) = (θ ^ m / r) * θ ^ k := by
    rw [zpow_add₀ hθ, zpow_natCast]
    ring
  simp only [jointExpectedTransformNorm, finiteTransform_scale, he]

end LpSelfSimilar.Fourier

namespace LpSelfSimilar.Entropy

/-- The actual maximizing band admits one block shift with exact support and frequency bounds. -/
theorem MaximizingBandFamily.exists_shift_with_frequency_control
    {ι : Type*} [Fintype ι] {z p : ι → ℝ}
    (F : MaximizingBandFamily z p) (hpsum : ∑ i, p i = 1) (j : ℝ)
    {θ r : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 70)
    (hr : 0 < r) :
    ∃ k : Fin (geometricPhaseLength θ + 1),
      (∀ ξ ε : ℝ, abs (|ξ| - 1) ≤ ε →
        Fourier.jointExpectedTransformNorm (F.joint j)
          (fun i ↦ θ ^ (Fourier.bandFirstShift θ ((2 : ℝ) ^ (-j)) r + (k.val : ℤ)) * z i)
          (ξ / r) ≤ 1 - F.cancellation j + 52 * ε) ∧
      (∀ label : Finset ι, ∃ b : ℝ, ∀ i, jointConditionalWeight (F.joint j) label i ≠ 0 →
        0 ≤ θ ^ (Fourier.bandFirstShift θ ((2 : ℝ) ^ (-j)) r + (k.val : ℤ)) * z i - b ∧
        θ ^ (Fourier.bandFirstShift θ ((2 : ℝ) ^ (-j)) r + (k.val : ℤ)) * z i - b ≤ 52 * r) := by
  classical
  let a : ℝ := (2 : ℝ) ^ (-j)
  let m : ℤ := Fourier.bandFirstShift θ a r
  let cover := graphIndependentCover (distanceBandGraph z a (16 * a))ᶜ
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hu : F.joint j ∈ supportedJointSpace p cover := F.supported j
  have hbase := Fourier.bandFirstShift_spec hθ0 hθ1 ha hr
  have hs : 0 < θ ^ m / r := div_pos (zpow_pos hθ0 _) hr
  obtain ⟨k, hk⟩ := F.exists_common_geometric_shift hpsum j hθ0 hθ1 hgap hs hbase.1.le hbase.2
  have hband : ∀ label i, i ∈ cover label → ∀ l, l ∈ cover label →
      i ≠ l → |z i - z l| < 16 * a := by
    intro label i hi l hl hil
    have hn := graphIndependentCover_isIndepSet (distanceBandGraph z a (16 * a))ᶜ
      label hi hl hil
    have he : (distanceBandGraph z a (16 * a)).Adj i l := by
      by_contra h
      exact hn ⟨hil, h⟩
    exact he.2.2
  have hdiam := Fourier.scaled_band_cover_diameter_le z cover hθ0 hθ1 hgap ha hr k.val hband
  have hkbase : Fourier.jointExpectedTransformNorm (F.joint j)
      (fun i ↦ θ ^ (m + (k.val : ℤ)) * z i) (1 / r) ≤ 1 - F.cancellation j := by
    rw [Fourier.jointExpectedTransformNorm_shift _ z hθ0.ne' m k.val r]
    exact hk
  refine ⟨k, ?_, ?_⟩
  · intro ξ ε hξ
    have h := Fourier.jointExpectedTransformNorm_frequency_band_le p cover hu hpsum
      (fun i ↦ θ ^ (m + (k.val : ℤ)) * z i) hr hdiam hξ
    exact h.trans (by linarith [hkbase])
  · intro label
    apply Geometry.exists_translation_of_nonzero_diameter
      (jointConditionalWeight (F.joint j) label)
      (fun i ↦ θ ^ (m + (k.val : ℤ)) * z i)
    intro i hi l hl
    have hic : i ∈ cover label := by
      by_contra h
      exact hi (jointConditionalWeight_eq_zero_of_not_mem p cover hu h)
    have hlc : l ∈ cover label := by
      by_contra h
      exact hl (jointConditionalWeight_eq_zero_of_not_mem p cover hu h)
    exact hdiam label i hic l hlc

end LpSelfSimilar.Entropy
