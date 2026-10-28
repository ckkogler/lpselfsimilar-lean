module

public import LpSelfSimilar.Probability.UniformReindex
public import LpSelfSimilar.Entropy.Bounds

@[expose] public section

/-!
A uniform independent summand gives a lower entropy bound when its digit map is
injective. Each atom of the sum receives at most one uniform atom for each value
of the other summand, so its mass is at most the inverse alphabet size. Averaging
the negative logarithm proves the lower bound. This elementary discrete argument
will retain sparse digits of an algebraic Bernoulli word.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LpSelfSimilar.Entropy

lemma finiteEntropy_ge_neg_log_of_atom_le {E : Type*} (p : PMF E)
    (hp : p.support.Finite) {C : ℝ} (_hC : 0 < C) (h : ∀ a, (p a).toReal ≤ C) :
    -Real.log C ≤ finiteEntropy p hp := by
  calc
    _ = ∑ a ∈ hp.toFinset, (p a).toReal * (-Real.log C) := by
      rw [← Finset.sum_mul, sum_support_toReal, one_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      have hpa : 0 < (p a).toReal :=
        ENNReal.toReal_pos (by simpa using ha) (p.apply_ne_top a)
      have hl := neg_le_neg (Real.log_le_log hpa (h a))
      simpa only [Real.negMulLog, mul_neg, neg_mul] using mul_le_mul_of_nonneg_left hl hpa.le

lemma uniformPMF_map_injective_atom_le {D E : Type*} [Fintype D] [Nonempty D]
    (Y : D → E) (hY : Function.Injective Y) (a : E) :
    (PMF.uniformOfFintype D).map Y a ≤ (Fintype.card D : ℝ≥0∞)⁻¹ := by
  classical
  by_cases h : ∃ d, Y d = a
  · obtain ⟨d, rfl⟩ := h
    rw [map_apply_of_injective _ hY]
    simp [PMF.uniformOfFintype_apply]
  · have hz : (PMF.uniformOfFintype D).map Y a = 0 := by
      rw [PMF.map_apply]
      rw [tsum_fintype]
      apply Finset.sum_eq_zero
      intro d _
      have hne : a ≠ Y d := fun he ↦ h ⟨d, he.symm⟩
      simp [hne]
    rw [hz]
    exact zero_le

lemma pairPMF_sum_map_apply {Ω D E : Type*} [Fintype Ω] [Fintype D]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace D] [MeasurableSingletonClass D] [AddCommGroup E]
    (p : PMF Ω) (q : PMF D) (X : Ω → E) (Y : D → E) (a : E) :
    (pairPMF p q).map (fun z ↦ X z.1 + Y z.2) a =
      ∑ i, p i * (q.map Y (a - X i)) := by
  classical
  simp only [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, pairPMF_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : a = X i + Y j
  · simp [h]
  · have he : a - X i ≠ Y j := by
      intro h'
      apply h
      rw [sub_eq_iff_eq_add] at h'
      simpa [add_comm] using h'
    simp [h, he]

/-- Any extra independent finite summand preserves the atom upper bound of an
injectively encoded uniform alphabet. -/
lemma independent_uniform_summand_atom_le {Ω D E : Type*} [Fintype Ω]
    [Fintype D] [Nonempty D] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace D] [MeasurableSingletonClass D] [AddCommGroup E]
    (p : PMF Ω) (X : Ω → E) (Y : D → E) (hY : Function.Injective Y) (a : E) :
    (pairPMF p (PMF.uniformOfFintype D)).map (fun z ↦ X z.1 + Y z.2) a ≤
      (Fintype.card D : ℝ≥0∞)⁻¹ := by
  rw [pairPMF_sum_map_apply]
  calc
    _ ≤ ∑ i, p i * (Fintype.card D : ℝ≥0∞)⁻¹ :=
      Finset.sum_le_sum (fun i _ ↦ mul_le_mul_right (uniformPMF_map_injective_atom_le Y hY _) _)
    _ = _ := by
      have hp : ∑ i : Ω, p i = 1 := by simpa only [tsum_fintype] using p.tsum_coe
      rw [← Finset.sum_mul, hp, one_mul]

/-- Entropy of the actual sum is at least the logarithm of the retained uniform
alphabet size, with all other summands and all output collisions allowed. -/
theorem entropy_ge_log_card_uniform_summand {Ω D E : Type*} [Fintype Ω]
    [Fintype D] [Nonempty D] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    [MeasurableSpace D] [MeasurableSingletonClass D] [AddCommGroup E]
    (p : PMF Ω) (X : Ω → E) (Y : D → E) (hY : Function.Injective Y) :
    Real.log (Fintype.card D) ≤
      finiteEntropy ((pairPMF p (PMF.uniformOfFintype D)).map (fun z ↦ X z.1 + Y z.2))
        (by
          simpa using (Set.toFinite (pairPMF p (PMF.uniformOfFintype D)).support).image
            (fun z ↦ X z.1 + Y z.2)) := by
  have hc : (0 : ℝ) < Fintype.card D := by positivity
  have h := finiteEntropy_ge_neg_log_of_atom_le
    ((pairPMF p (PMF.uniformOfFintype D)).map (fun z ↦ X z.1 + Y z.2))
    (by
      simpa using (Set.toFinite (pairPMF p (PMF.uniformOfFintype D)).support).image
        (fun z ↦ X z.1 + Y z.2))
    (inv_pos.mpr hc) (fun a ↦ ?_)
  · simpa only [Real.log_inv, neg_neg] using h
  · have hb := independent_uniform_summand_atom_le p X Y hY a
    have ht := ENNReal.toReal_mono (by simp) hb
    simpa using ht

end LpSelfSimilar.Entropy
