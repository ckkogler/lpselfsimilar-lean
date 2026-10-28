module

public import LpSelfSimilar.WeakReverseHolder.SharpConstants
public import LpSelfSimilar.WeakReverseHolder.SharpTail
public import LpSelfSimilar.WeakReverseHolder.SharpMoments

/-!
# The sharp weak reverse Hölder criterion

This is Kittle–Kogler, Lemma 2.1, with `C = 18^d` and exponent
`1 + log (1 / (C * η)) / log (C / ε)`.

The proof uses dyadic stopping balls instead of largest-radius balls. Their
eightfold enlargements give the contraction `2 * 8^d * η`; the strict numerical
margin relative to `18^d * η` retains the full stated exponent. The original
criterion and its public definitions remain unchanged.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar

theorem weak_reverse_holder_eighteen_of_measurable {d : ℕ} (hd : 1 ≤ d)
    {f : Space d → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    (hfm : Measurable f) {ε η : ℝ} (hε : ε ∈ Ioo 0 1)
    (hη : η ∈ Ioo 0 (sharpCoveringConstant d)⁻¹)
    (hsmall : SmallSetHypothesis f ε η) :
    1 < sharpLemmaExponent d ε η ∧
      MemLp f (ENNReal.ofReal (sharpLemmaExponent d ε η)) volume := by
  have hp := one_lt_sharpLemmaExponent hd hε.1 hε.2 hη.1 hη.2
  have hA := one_lt_sharp_expansion hd hε.1 hε.2
  have hA2 : 2 < sharpCoveringConstant d / ε := by
    rw [lt_div_iff₀ hε.1]
    linarith [eighteen_le_sharpCoveringConstant hd, hε.2]
  have hAε : 2 ≤ (sharpCoveringConstant d / ε) * ε := by
    rw [div_mul_cancel₀ _ hε.1.ne']
    linarith [eighteen_le_sharpCoveringConstant hd]
  refine ⟨hp, sharp_memLp_of_density_tail_contraction volume hfm hf_nonneg hf
    hA (sharpStoppingThreshold_pos hf_nonneg) hp
    (sharp_summation_ratio_lt_one hd hε.1 hε.2 hη.1 hη.2) ?_⟩
  intro t ht
  exact sharp_density_tail_contraction hf hfm hf_nonneg hA2 hη.1.le hAε hsmall ht

/-- Kittle–Kogler's sharp weak reverse Hölder criterion, including the exact
dimension constant, exponent, and full allowed range of the small-set parameters. -/
theorem weak_reverse_holder_eighteen {d : ℕ} (hd : 1 ≤ d)
    {f : Space d → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (hf : Integrable f volume)
    {ε η : ℝ} (hε : ε ∈ Ioo 0 1)
    (hη : η ∈ Ioo 0 (sharpCoveringConstant d)⁻¹)
    (hsmall : SmallSetHypothesis f ε η) :
    1 < sharpLemmaExponent d ε η ∧
      MemLp f (ENNReal.ofReal (sharpLemmaExponent d ε η)) volume := by
  let g : Space d → ℝ := fun x => max 0 (hf.aestronglyMeasurable.mk f x)
  have hgm : Measurable g := measurable_const.max hf.aestronglyMeasurable.measurable_mk
  have hg0 (x : Space d) : 0 ≤ g x := le_max_left _ _
  have heq : f =ᵐ[volume] g := by
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk] with x hx
    simp only [g, ← hx, max_eq_right (hf_nonneg x)]
  have hgi : Integrable g volume := hf.congr heq
  have hset (E : Set (Space d)) : (∫ x in E, g x) = ∫ x in E, f x :=
    integral_congr_ae (ae_restrict_of_ae heq.symm)
  have hgsmall : SmallSetHypothesis g ε η := by
    intro x r hr hr1 E hE hsub hvol
    rw [hset, hset]
    exact hsmall x r hr hr1 E hE hsub hvol
  obtain ⟨hp, hgp⟩ := weak_reverse_holder_eighteen_of_measurable hd hg0 hgi hgm
    hε hη hgsmall
  exact ⟨hp, (memLp_congr_ae heq).mpr hgp⟩

end LpSelfSimilar
