module

public import LpSelfSimilar.Analysis.FiniteYoungConvolution
public import LpSelfSimilar.Analysis.ScaledDensity
public import LpSelfSimilar.Analysis.ContinuousDensitySupport

/-!
# Young's inequality for scaled measures

Lemma 3.2 of Kittle–Kogler applies to any compactly supported probability law.
We lower the density exponent on a compact carrier, apply the finite Young
inequality to the scaled factors, and recover compact support of the continuous
density from a compact carrier of their convolution.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace LpSelfSimilar.Revised

/-- Compact carriers are preserved by convolution. -/
lemma exists_compact_carrier_conv (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    (hμ : ∃ K : Set ℝ, IsCompact K ∧ μ Kᶜ = 0)
    (hν : ∃ K : Set ℝ, IsCompact K ∧ ν Kᶜ = 0) :
    ∃ K : Set ℝ, IsCompact K ∧ (μ ∗ ν) Kᶜ = 0 := by
  obtain ⟨K, hK, hμK⟩ := hμ
  obtain ⟨L, hL, hνL⟩ := hν
  let S := (fun z : ℝ × ℝ ↦ z.1 + z.2) '' (K ×ˢ L)
  have hS : IsCompact S := (hK.prod hL).image (by fun_prop)
  refine ⟨S, hS, ?_⟩
  have hKae : ∀ᵐ x ∂μ, x ∈ K := ae_iff.mpr hμK
  have hLae : ∀ᵐ x ∂ν, x ∈ L := ae_iff.mpr hνL
  have hae : ∀ᵐ z ∂μ.prod ν, z ∈ K ×ˢ L := by
    apply (ae_prod_iff_ae_ae (hK.measurableSet.prod hL.measurableSet)).mpr
    filter_upwards [hKae] with x hx
    filter_upwards [hLae] with y hy
    exact ⟨hx, hy⟩
  have hsum : ∀ᵐ x ∂(μ ∗ ν), x ∈ S := by
    rw [Measure.conv]
    apply (ae_map_iff (by fun_prop) hS.measurableSet).mpr
    filter_upwards [hae] with z hz
    exact ⟨z, hz, rfl⟩
  exact ae_iff.mp hsum

/-- A finite convolution of compactly carried finite measures has a compact carrier. -/
lemma exists_compact_carrier_finiteConvolution {n : ℕ} (μ : Fin n → Measure ℝ)
    (hfinite : ∀ i, IsFiniteMeasure (μ i))
    (hcompact : ∀ i, ∃ K : Set ℝ, IsCompact K ∧ μ i Kᶜ = 0) :
    IsFiniteMeasure (finiteConvolution μ) ∧
      ∃ K : Set ℝ, IsCompact K ∧ finiteConvolution μ Kᶜ = 0 := by
  induction n with
  | zero =>
      refine ⟨by dsimp [finiteConvolution]; infer_instance, {0}, isCompact_singleton, ?_⟩
      simp [finiteConvolution]
  | succ n ih =>
      obtain ⟨hI, hK⟩ := ih (fun i ↦ μ i.succ) (fun i ↦ hfinite i.succ)
        (fun i ↦ hcompact i.succ)
      let _ := hfinite 0
      let _ := hI
      exact ⟨by dsimp [finiteConvolution]; infer_instance,
        exists_compact_carrier_conv _ _ (hcompact 0) hK⟩

/-- Lemma 3.2: arbitrary positive scaled copies of a compactly supported
probability law with density in `L^p`, `p ≥ k/(k-1)`, convolve to a continuous
compactly supported density. A compact carrier states compact support without
making any regularity assumption on the original density representative.
The exponent may be infinite. -/
theorem scaled_finite_convolution_continuous_density_ennreal {k : ℕ} (hk : 2 ≤ k)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcompact : ∃ K : Set ℝ, IsCompact K ∧ ν Kᶜ = 0)
    {p : ℝ≥0∞} (hp : ENNReal.ofReal ((k : ℝ) / ((k : ℝ) - 1)) ≤ p)
    {f : ℝ → ℝ} (hf : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    (hν : ν = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hfp : MemLp f p volume)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ g : ℝ → ℝ, (∀ x, 0 ≤ g x) ∧ Continuous g ∧ HasCompactSupport g ∧
      finiteConvolution (fun i ↦ ν.map (fun x ↦ a i * x)) =
        volume.withDensity (fun x ↦ ENNReal.ofReal (g x)) := by
  obtain ⟨K, hK, hνK⟩ := hcompact
  obtain ⟨F, hF0, hF, hνF, hFp, _⟩ := exists_supported_density_memLp hf hf0 hν
    hK.measurableSet hνK hK.measure_lt_top.ne hfp hp
  let μ : Fin k → Measure ℝ := fun i ↦ ν.map (fun x ↦ a i * x)
  have hfamily (i : Fin k) := exists_density_map_mul_pos (ha i) hF hF0 hνF hFp
  obtain ⟨g, hg0, hgc, hgi, hμg⟩ := exists_continuous_density_finiteConvolution hk μ
    (by intro i; simpa only [convolutionExponent, Nat.cast_one] using hfamily i)
  have hμcompact (i : Fin k) : ∃ S : Set ℝ, IsCompact S ∧ μ i Sᶜ = 0 := by
    let S := (fun x : ℝ ↦ a i * x) '' K
    have hS : IsCompact S := hK.image (by fun_prop)
    refine ⟨S, hS, ?_⟩
    rw [Measure.map_apply (by fun_prop) hS.measurableSet.compl]
    apply measure_mono_null _ hνK
    intro x hx hxK
    exact hx ⟨x, hxK, rfl⟩
  obtain ⟨_, S, hS, hμS⟩ := exists_compact_carrier_finiteConvolution μ
    (fun i ↦ by dsimp [μ]; infer_instance) hμcompact
  exact ⟨g, hg0, hgc, hasCompactSupport_of_density hgi hg0 hgc hμg hS hμS, hμg⟩

/-- The finite real-exponent formulation of Lemma 3.2. -/
theorem scaled_finite_convolution_continuous_density {k : ℕ} (hk : 2 ≤ k)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcompact : ∃ K : Set ℝ, IsCompact K ∧ ν Kᶜ = 0)
    {p : ℝ} (hp : (k : ℝ) / ((k : ℝ) - 1) ≤ p)
    {f : ℝ → ℝ} (hf : Integrable f volume) (hf0 : ∀ x, 0 ≤ f x)
    (hν : ν = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hfp : MemLp f (ENNReal.ofReal p) volume)
    (a : Fin k → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ g : ℝ → ℝ, (∀ x, 0 ≤ g x) ∧ Continuous g ∧ HasCompactSupport g ∧
      finiteConvolution (fun i ↦ ν.map (fun x ↦ a i * x)) =
        volume.withDensity (fun x ↦ ENNReal.ofReal (g x)) :=
  scaled_finite_convolution_continuous_density_ennreal hk ν hcompact
    (ENNReal.ofReal_le_ofReal hp) hf hf0 hν hfp a ha

end LpSelfSimilar.Revised
