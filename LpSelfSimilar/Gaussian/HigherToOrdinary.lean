module

public import LpSelfSimilar.Gaussian.VarianceTaylorNorm
public import LpSelfSimilar.Gaussian.HigherDetailNorm
public import LpSelfSimilar.Analysis.TaylorCoefficientBounds

@[expose] public section

/-!
A finite-variance comparison between higher and ordinary Gaussian detail.

Taylor expansion from a larger variance bounds the endpoint terms by universal
Gaussian norms. The small higher-detail bound controls the integrated remainder.
Using a finite interval avoids any assumption about derivatives at infinite
variance; both endpoint and remainder constants grow at most exponentially.
-/

open MeasureTheory MeasureTheory.Measure Real Set

namespace LpSelfSimilar.Gaussian

private lemma taylor_boundary_term_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (j : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (b - a) ^ j / (j.factorial : ℝ) * (∫ x, |higherSmooth μ (j + 1) b x|) ≤
      ((j + 1 : ℝ) ^ (j + 1) / (j.factorial : ℝ)) / (detailNormalization * b) := by
  have hb := ha.trans_le hab
  have hQ := detailNormalization_pos
  have hf : (0 : ℝ) < (j.factorial : ℝ) := Nat.cast_pos.mpr j.factorial_pos
  have hn := integral_abs_higherSmooth_universal μ (Nat.succ_pos j) hb
  simp only [Nat.cast_succ, Nat.succ_eq_add_one] at hn
  calc
    _ ≤ (b - a) ^ j / (j.factorial : ℝ) *
        ((j + 1 : ℝ) ^ (j + 1) / (detailNormalization * b ^ (j + 1))) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ ≤ b ^ j / (j.factorial : ℝ) *
        ((j + 1 : ℝ) ^ (j + 1) / (detailNormalization * b ^ (j + 1))) := by
      gcongr
      linarith
    _ = _ := by rw [pow_succ]; field_simp; ring

/-- Small order-`n+2` detail on a finite variance interval controls ordinary
detail at its lower endpoint. All constants are absolute. -/
theorem detail_le_of_higherDetail_interval (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (n : ℕ) {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 ≤ δ)
    (h : ∀ y ∈ Icc a b, higherDetail μ (n + 2) (sqrt (y / (n + 2))) ≤ δ) :
    detail μ (sqrt a) ≤ (10 : ℝ) ^ (n + 2) * (δ + a / b) := by
  have hb := ha.trans_le hab
  have hQ := detailNormalization_pos
  let D : ℝ := δ * (n + 2 : ℝ) ^ (n + 2) / detailNormalization
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hD (y : ℝ) (hy : y ∈ Icc a b) :
      (∫ x, |higherSmooth μ (n + 2) y x|) ≤ D / y ^ (n + 2) := by
    have hi := integral_abs_higherSmooth_le_of_higherDetail μ
      (by omega : 0 < n + 2) (ha.trans_le hy.1)
      (by simpa only [Nat.cast_add, Nat.cast_ofNat] using h y hy)
    simp only [Nat.cast_add, Nat.cast_ofNat] at hi
    exact hi.trans_eq (by dsimp [D]; ring)
  have ht := integral_abs_firstSmooth_le_taylor μ n ha hab hD0 hD
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range (n + 1)) ↦
    taylor_boundary_term_le μ j ha hab)
  rw [← Finset.sum_div] at hs
  have hs' := hs.trans (div_le_div_of_nonneg_right (sum_gaussian_taylor_coefficients_le n)
    (mul_nonneg hQ.le hb.le))
  have hc : (n + 2 : ℝ) ^ (n + 2) / ((n + 1).factorial : ℝ) ≤
      (10 : ℝ) ^ (n + 2) := by
    have hc := gaussian_taylor_coefficient_le_six_pow (n + 1)
    simp only [Nat.cast_add, Nat.cast_one] at hc
    have hp : (6 : ℝ) ^ (n + 2) ≤ 10 ^ (n + 2) := by gcongr; norm_num
    simpa only [add_assoc, one_add_one_eq_two] using hc.trans hp
  have hnorm : detail μ (sqrt a) = a * detailNormalization *
      (∫ x, |firstSmooth μ a x|) := by
    unfold detail firstSmooth
    rw [sq_sqrt ha.le]
  rw [hnorm]
  calc
    _ ≤ a * detailNormalization *
        ((10 : ℝ) ^ (n + 2) / (detailNormalization * b) +
          D / ((n + 1).factorial * a)) :=
      mul_le_mul_of_nonneg_left (ht.trans (add_le_add hs' le_rfl)) (by positivity)
    _ = (10 : ℝ) ^ (n + 2) * (a / b) +
        δ * ((n + 2 : ℝ) ^ (n + 2) / ((n + 1).factorial : ℝ)) := by
      dsimp [D]
      field_simp <;> ring
    _ ≤ (10 : ℝ) ^ (n + 2) * (a / b) + δ * (10 : ℝ) ^ (n + 2) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hc hδ)
    _ = _ := by ring

end LpSelfSimilar.Gaussian
