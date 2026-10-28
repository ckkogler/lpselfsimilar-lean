module

public import LpSelfSimilar.Bernoulli.PackingConditionalDecomposition
public import LpSelfSimilar.Bernoulli.ConditionalBlockDerivatives

@[expose] public section

/-!
# Averaged derivative bounds for the constructed multiscale packing

The actual packing provides every block, its original label PMF, and a translation
placing each conditional support in `[0,52]` after normalization. Translations
are chosen once for all frequencies. The proved averaged Leibniz estimate and
the packing count and attenuation budget give exactly
`(80*L*T/chi)^k * exp(-a_*T)` through order two. The original, untranslated
mixture identity is retained separately from the normalized analytic estimates.
-/

open MeasureTheory MeasureTheory.Measure Set
open scoped BigOperators
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- The constructed packing has the exact averaged derivative estimate with original label weights. -/
theorem exists_packing_normalized_derivative_bounds {θ ρ L R : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hgap : -Real.log θ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (hsmall : (-Real.log θ) * (packingLogScale (L / ρ)) ^ 2 ≤ ρ / 2)
    (hR : packingScaleThreshold (-Real.log θ) ρ L ≤ R)
    (hentropy : ∀ n : ℕ, 0 < n →
      ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ n : ℕ, 0 < n → ∀ x ∈ (digitPMF θ n).support,
      ∀ y ∈ (digitPMF θ n).support, x ≠ y → (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let T := packingLengthCount (-Real.log θ) ρ L R
    ∃ (m : ℕ) (scale : Fin m → Fin T) (j : Fin m → ℝ) (start : Fin m → ℕ) (η : Measure ℝ),
      let len := fun i ↦ packingBlockLength (-Real.log θ) (L / ρ) (scale i)
      let b := fun i ↦ digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) (len i) (j i)
      ∃ c : (i : Fin m) → Finset (digitPMF_support_finite θ (len i)).toFinset → ℝ,
        (m : ℝ) ≤ L * T / (-Real.log θ) ∧
        (∀ i, 0 < b i ∧ b i ≤ 1 - Real.sqrt (7 / 16)) ∧
        Function.Surjective scale ∧
        (∀ i l, i ≠ l → Disjoint
          (Finset.Ico (start i) (start i + len i)) (Finset.Ico (start l) (start l + len l))) ∧
        (∀ i, ∀ d < len i, 2 < R - (-Real.log θ / Real.log 2) * (start i + d : ℕ)) ∧
        packingAttenuation (-Real.log θ) ρ L * T ≤ ∑ i, b i ∧
        (∀ i label, ((digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) label).map
          (fun y ↦ (y - c i label) / (2 : ℝ) ^ (-R))) (Icc 0 52) = 1) ∧
        IsProbabilityMeasure η ∧
        convolution θ =
          pmfMixture (productPMF (fun i ↦ digitBandLabelPMF θ (len i) (j i)))
            (fun ω ↦ finiteConvolution
              (fun i ↦ digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) (ω i))) ∗ η ∧
        (∀ ξ : ℝ, abs (|ξ| - 1) ≤ packingFrequencyWidth (L / ρ) →
          ∀ k : ℕ, k ≤ 2 →
          (∫ ω, ‖iteratedDeriv k (charFun (finiteConvolution (fun i ↦
              (digitBandShiftedLaw θ (len i) (j i) (start i : ℤ) (ω i)).map
                (fun y ↦ (y - c i (ω i)) / (2 : ℝ) ^ (-R))))) ξ‖
            ∂(productPMF (fun i ↦ digitBandLabelPMF θ (len i) (j i))).toMeasure) ≤
              (80 * L * T / (-Real.log θ)) ^ k *
                Real.exp (-(packingAttenuation (-Real.log θ) ρ L * T))) := by
  classical
  obtain ⟨m, scale, j, start, η, hcount, hb, hscale, hd, hcoord,
    hbudget, hfreq, hs, hη, heq, _⟩ := exists_packing_conditional_decomposition
      hθ0 hθ1 hgap hρ hρ1 hL hC hsmall hR hentropy hsep
  let T := packingLengthCount (-Real.log θ) ρ L R
  let len := fun i ↦ packingBlockLength (-Real.log θ) (L / ρ) (scale i)
  let b := fun i ↦ digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) (len i) (j i)
  choose c hc using hs
  refine ⟨m, scale, j, start, η, c, hcount, hb, hscale, hd, hcoord, hbudget, hc, hη, heq, ?_⟩
  intro ξ hξ k hk
  have h := integral_norm_iteratedDeriv_normalized_conditionals_le
    (fun i ↦ digitBandLabelPMF θ (len i) (j i))
    (fun i ↦ digitBandShiftedLaw θ (len i) (j i) (start i : ℤ)) b c ((2 : ℝ) ^ (-R))
    (fun i ↦ (hb i).1.le) (fun i ↦ (hb i).2) hc ξ
    (fun i ↦ by
      rw [integral_norm_charFun_digitBandLabelPMF]
      exact hfreq i ξ hξ) k hk
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hcost : 80 * (m : ℝ) ≤ 80 * L * T / (-Real.log θ) := by
    calc
      _ ≤ 80 * (L * T / (-Real.log θ)) :=
        mul_le_mul_of_nonneg_left hcount (by norm_num)
      _ = _ := by ring
  have hL0 : 0 ≤ L := by linarith
  exact h.trans (mul_le_mul
    (pow_le_pow_left₀ (by positivity) hcost k)
    (Real.exp_le_exp.mpr (neg_le_neg hbudget))
    (Real.exp_pos _).le (pow_nonneg (by positivity) k))

end LpSelfSimilar.Bernoulli
