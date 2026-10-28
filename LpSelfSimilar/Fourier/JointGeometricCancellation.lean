module

public import LpSelfSimilar.Fourier.ConditionalCancellation
public import LpSelfSimilar.Fourier.GeometricCancellation
public import LpSelfSimilar.Entropy.DyadicBandFamily

@[expose] public section

/-!
# Geometric shifts of the attained band conditionals

Every allowed conditional support lies in the same distance band. The original
label masses average the finite-law attenuation, and one common geometric shift
attains that average. Specializing to the previously constructed maximizing
families connects their integrated cancellation budget to actual Fourier norms.
-/

open scoped BigOperators
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Fourier

/-- A distance-band conditional decomposition has the exact averaged geometric attenuation. -/
theorem weighted_jointExpectedTransformNorm_le_of_band {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (hpsum : ∑ i, p i = 1) (z : ι → ℝ)
    {θ a s₀ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 70)
    (hs : 0 < s₀) (hbase0 : Real.pi ≤ s₀ * a) (hbase1 : s₀ * a ≤ Real.pi / θ)
    (hband : ∀ j i, i ∈ cover j → ∀ l, l ∈ cover j → i ≠ l →
      a ≤ |z i - z l| ∧ |z i - z l| < 16 * a) :
    (∑ k : Fin (geometricPhaseLength θ + 1),
      geometricWeight θ (geometricPhaseLength θ) k *
        jointExpectedTransformNorm u z (s₀ * θ ^ (k : ℕ))) ≤
      1 - jointExpectedCancellation u := by
  have hcol (j : κ) : jointLabelWeight u j *
      (∑ k : Fin (geometricPhaseLength θ + 1),
        geometricWeight θ (geometricPhaseLength θ) k *
          ‖finiteTransform (jointConditionalWeight u j) z (s₀ * θ ^ (k : ℕ))‖) ≤
      jointLabelWeight u j *
        (1 - finiteCancellation Finset.univ (jointConditionalWeight u j)) := by
    by_cases hq : jointLabelWeight u j = 0
    · simp [hq]
    have hqpos : 0 < jointLabelWeight u j :=
      lt_of_le_of_ne (jointLabelWeight_nonneg u hu.1 j) (by intro h; exact hq h.symm)
    apply mul_le_mul_of_nonneg_left _ hqpos.le
    apply geometric_norm_finiteTransform_le_of_band (jointConditionalWeight u j) z
      (jointConditionalWeight_nonneg u hu.1 j)
      (sum_jointConditionalWeight_eq_one u j hqpos) hθ0 hθ1 hgap hs hbase0 hbase1
    intro i l hil hi hl
    have hic : i ∈ cover j := by
      by_contra h
      exact hi (jointConditionalWeight_eq_zero_of_not_mem p cover hu h)
    have hlc : l ∈ cover j := by
      by_contra h
      exact hl (jointConditionalWeight_eq_zero_of_not_mem p cover hu h)
    exact hband j i hic l hlc hil
  rw [weighted_jointExpectedTransformNorm_eq]
  calc
    _ ≤ ∑ j, jointLabelWeight u j *
        (1 - finiteCancellation Finset.univ (jointConditionalWeight u j)) :=
      Finset.sum_le_sum fun j _ ↦ hcol j
    _ = 1 - jointExpectedCancellation u := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib,
        sum_jointLabelWeight_eq_one p cover hu hpsum, jointExpectedCancellation]

/-- A common geometric shift is chosen before sampling the original conditional label. -/
theorem exists_common_geometric_shift_of_band {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (cover : κ → Finset ι) {u : ι → κ → ℝ}
    (hu : u ∈ supportedJointSpace p cover) (hpsum : ∑ i, p i = 1) (z : ι → ℝ)
    {θ a s₀ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 70)
    (hs : 0 < s₀) (hbase0 : Real.pi ≤ s₀ * a) (hbase1 : s₀ * a ≤ Real.pi / θ)
    (hband : ∀ j i, i ∈ cover j → ∀ l, l ∈ cover j → i ≠ l →
      a ≤ |z i - z l| ∧ |z i - z l| < 16 * a) :
    ∃ k : Fin (geometricPhaseLength θ + 1),
      jointExpectedTransformNorm u z (s₀ * θ ^ (k : ℕ)) ≤
        1 - jointExpectedCancellation u :=
  Analysis.exists_le_of_weighted_sum_le
    (geometricWeight θ (geometricPhaseLength θ))
    (fun k ↦ jointExpectedTransformNorm u z (s₀ * θ ^ (k : ℕ)))
    (geometricWeight_nonneg hθ0.le hθ1.le _) (sum_geometricWeight_eq_one θ _)
    (weighted_jointExpectedTransformNorm_le_of_band p cover hu hpsum z
      hθ0 hθ1 hgap hs hbase0 hbase1 hband)

end LpSelfSimilar.Fourier

namespace LpSelfSimilar.Entropy

/-- The actual maximizing band family has a common shift with its recorded cancellation. -/
theorem MaximizingBandFamily.exists_common_geometric_shift {ι : Type*} [Fintype ι]
    {z p : ι → ℝ} (F : MaximizingBandFamily z p) (hpsum : ∑ i, p i = 1) (j : ℝ)
    {θ s₀ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 70)
    (hs : 0 < s₀) (hbase0 : Real.pi ≤ s₀ * (2 : ℝ) ^ (-j))
    (hbase1 : s₀ * (2 : ℝ) ^ (-j) ≤ Real.pi / θ) :
    ∃ k : Fin (geometricPhaseLength θ + 1),
      Fourier.jointExpectedTransformNorm (F.joint j) z (s₀ * θ ^ (k : ℕ)) ≤
        1 - F.cancellation j := by
  classical
  apply Fourier.exists_common_geometric_shift_of_band p _ (F.supported j) hpsum z
    hθ0 hθ1 hgap hs hbase0 hbase1
  intro label i hi l hl hil
  have hn := graphIndependentCover_isIndepSet
    (distanceBandGraph z ((2 : ℝ) ^ (-j)) (16 * (2 : ℝ) ^ (-j)))ᶜ label hi hl hil
  have he : (distanceBandGraph z ((2 : ℝ) ^ (-j))
      (16 * (2 : ℝ) ^ (-j))).Adj i l := by
    by_contra h
    exact hn ⟨hil, h⟩
  exact he.2

end LpSelfSimilar.Entropy
