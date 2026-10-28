module

public import LpSelfSimilar.Rational.GridEntropy
public import LpSelfSimilar.Rational.Parameters
public import LpSelfSimilar.Bernoulli.FiniteBounds
public import LpSelfSimilar.Entropy.GridBounds
public import LpSelfSimilar.Entropy.LogScale

@[expose] public section

/-!
The two entropy endpoints for rational digit blocks. Integer separation gives
full entropy at fine scales, while the geometric support interval controls
coarse entropy. Every bound is uniform in the reduced numerator.
-/

open MeasureTheory Set Real LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Rational

lemma digit_entropyOnLogScale_eq {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hab : a.Coprime b) (n : ℕ) {x : ℝ} (hx : complexity b * n ≤ x) :
    entropyOnLogScale (digitPMF ((a : ℝ) / b) n) (digitPMF_support_finite _ _) x =
      (n : ℝ) * Real.log 2 := by
  apply digit_gridEntropy ha (by omega) hab n (Real.exp_pos _)
  exact (Real.exp_le_exp.mpr (by linarith)).trans (exp_neg_complexity_mul_le hb)

lemma digit_entropyOnLogScale_le_support {r x : ℝ} (hr₀ : 0 ≤ r) (hr₁ : r < 1)
    (hx : 0 ≤ x) (n : ℕ) :
    entropyOnLogScale (digitPMF r n) (digitPMF_support_finite _ _) x ≤
      x + Real.log 4 + Real.log ((1 - r)⁻¹) := by
  have hgap : 0 < 1 - r := sub_pos.mpr hr₁
  let K := (1 - r)⁻¹
  have hK : 0 < K := inv_pos.mpr (sub_pos.mpr hr₁)
  have hK1 : 1 ≤ K := (one_le_inv₀ (sub_pos.mpr hr₁)).mpr (by linarith)
  have he1 : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  have hbase := gridEntropy_le_log_length (digitPMF r n) (digitPMF_support_finite _ _)
    (digitPMF_support_subset_interval hr₀ hr₁ n) (Real.exp_pos (-x))
  change gridEntropy (digitPMF r n) _ (Real.exp (-x)) ≤ _
  apply hbase.trans
  have harg : ((1 - r)⁻¹ - -(1 - r)⁻¹) / Real.exp (-x) + 2 ≤
      4 * K * Real.exp x := by
    rw [Real.exp_neg, div_inv_eq_mul]
    dsimp only [K] at hK1 ⊢
    nlinarith [mul_le_mul hK1 he1 (by norm_num : (0 : ℝ) ≤ 1) hK.le]
  calc
    Real.log (((1 - r)⁻¹ - -(1 - r)⁻¹) / Real.exp (-x) + 2) ≤
        Real.log (4 * K * Real.exp x) := Real.log_le_log (by rw [sub_neg_eq_add]; positivity) harg
    _ = _ := by
      rw [Real.log_mul (by positivity : 4 * K ≠ 0) (Real.exp_ne_zero _),
        Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hK.ne', Real.log_exp]
      dsimp only [K]
      ring

lemma digit_entropyOnLogScale_le_complexity {a b : ℕ} (hb : 2 ≤ b)
    (hr₀ : 0 ≤ (a : ℝ) / b) (hr₁ : (a : ℝ) / b < 1)
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    entropyOnLogScale (digitPMF ((a : ℝ) / b) n) (digitPMF_support_finite _ _) x ≤
      x + Real.log 4 + complexity b := by
  have hab : a < b := by
    exact_mod_cast (div_lt_one (by positivity : (0 : ℝ) < b)).mp hr₁
  have hlog := log_inverse_gap_le hb hab
  rw [one_div] at hlog
  have h := digit_entropyOnLogScale_le_support hr₀ hr₁ hx n
  linarith

end LpSelfSimilar.Rational
