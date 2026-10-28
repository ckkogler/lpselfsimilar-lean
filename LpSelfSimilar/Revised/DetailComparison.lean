module

public import LpSelfSimilar.Gaussian.DetailDecay
public import LpSelfSimilar.Gaussian.HigherDetail

/-!
# Higher-to-first detail comparison

Lemma 3.4 of Kittle–Kogler is obtained by changing from variance to radius in
the established integral comparison. Order one is treated directly, so the
statement covers every positive derivative order.
-/

@[expose] public section

open MeasureTheory Real Set

namespace LpSelfSimilar.Revised

/-- A bound on the higher detail throughout the radius interval gives the
paper's ordinary-detail bound, including order one. -/
theorem detail_le_of_higherDetail_radius (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {k : ℕ} (hk : 1 ≤ k) {r b δ : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hrb : r / sqrt (k : ℝ) ≤ b) (hδ : 0 ≤ δ)
    (h : ∀ t ∈ Icc (r / sqrt (k : ℝ)) b, Gaussian.higherDetail μ k t ≤ δ) :
    Gaussian.detail μ r ≤ (10 : ℝ) ^ k * (δ + r ^ 2 / b ^ 2) := by
  by_cases hk1 : k = 1
  · subst k
    have hrb' : r ≤ b := by simpa using hrb
    have ht := h r ⟨by simp, hrb'⟩
    rw [Gaussian.higherDetail_one μ hr] at ht
    have ht0 := Gaussian.detail_nonneg μ r
    have htail : 0 ≤ r ^ 2 / b ^ 2 := by positivity
    norm_num
    linarith
  · have hk2 : 2 ≤ k := by omega
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hsqrt : 0 < sqrt (k : ℝ) := sqrt_pos.mpr hk0
    have hr_le : r ≤ b * sqrt (k : ℝ) := (div_le_iff₀ hsqrt).mp hrb
    have hab : r ^ 2 ≤ (k : ℝ) * b ^ 2 := by
      have hh := sq_le_sq₀ hr.le (by positivity : 0 ≤ b * sqrt (k : ℝ)) |>.2 hr_le
      simpa only [mul_pow, sq_sqrt hk0.le, mul_comm] using hh
    have hinterval (y : ℝ) (hy : y ∈ Icc (r ^ 2) ((k : ℝ) * b ^ 2)) :
        Gaussian.higherDetail μ k (sqrt (y / (k : ℝ))) ≤ δ := by
      apply h
      constructor
      · rw [sqrt_div ((sq_nonneg r).trans hy.1)]
        have hs : r ≤ sqrt y := by
          simpa only [sqrt_sq hr.le] using sqrt_le_sqrt hy.1
        exact div_le_div_of_nonneg_right hs hsqrt.le
      · apply (sqrt_le_iff).mpr
        exact ⟨hb.le, (div_le_iff₀ hk0).mpr (by nlinarith [hy.2])⟩
    have hcomparison := Gaussian.detail_le_of_higherDetail_order μ hk2
      (sq_pos_of_pos hr) hab hδ hinterval
    rw [sqrt_sq hr.le] at hcomparison
    apply hcomparison.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hden : b ^ 2 ≤ (k : ℝ) * b ^ 2 := by nlinarith [sq_nonneg b]
    have htail : r ^ 2 / ((k : ℝ) * b ^ 2) ≤ r ^ 2 / b ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg r) (sq_pos_of_pos hb) hden
    exact add_le_add le_rfl htail

/-- Lemma 3.4 in its literal supremum formulation. The supremum is over the
closed interval of radii, and the universal higher-detail bound makes it finite. -/
theorem detail_le_sup_higherDetail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {k : ℕ} (hk : 1 ≤ k) {r b : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hrb : r / sqrt (k : ℝ) ≤ b) :
    Gaussian.detail μ r ≤ (10 : ℝ) ^ k *
      (sSup (Gaussian.higherDetail μ k '' Icc (r / sqrt (k : ℝ)) b) + r ^ 2 / b ^ 2) := by
  let S := Gaussian.higherDetail μ k '' Icc (r / sqrt (k : ℝ)) b
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlo : 0 < r / sqrt (k : ℝ) := div_pos hr (sqrt_pos.mpr hk0)
  have hS : BddAbove S := by
    refine ⟨1, ?_⟩
    rintro x ⟨t, ht, rfl⟩
    exact Gaussian.higherDetail_le_one μ hk (hlo.trans_le ht.1)
  have hmem : Gaussian.higherDetail μ k (r / sqrt (k : ℝ)) ∈ S :=
    ⟨_, ⟨le_rfl, hrb⟩, rfl⟩
  have hnonneg : 0 ≤ sSup S :=
    (Gaussian.higherDetail_nonneg _ _ _).trans (le_csSup hS hmem)
  exact detail_le_of_higherDetail_radius μ hk hr hb hrb hnonneg
    (fun t ht ↦ le_csSup hS ⟨t, ht, rfl⟩)

end LpSelfSimilar.Revised
