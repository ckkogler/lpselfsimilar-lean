module

public import LpSelfSimilar.Algebraic.ArithmeticInput
public import LpSelfSimilar.Bernoulli.EntropySupport

@[expose] public section

/-!
The exact entropy endpoints for revised Lemma 3.7.

At logarithmic scales beyond 2Bn the actual atoms are resolved and entropy is at
least n/(8B). On the coarse boundary interval starting at n/(32B), the proved
support and logarithmic-gap bounds give entropy at most n/(16B), whenever
n>=100B^2. No rational word-injectivity hypothesis is used.
-/

open MeasureTheory Set Real
open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Algebraic

lemma digit_entropyOnLogScale_lower {r : ℝ} (hr : IsAlgebraic ℚ r)
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) {x : ℝ} (hx : complexity r * n ≤ x) :
    (n : ℝ) / (8 * complexity r) ≤
      entropyOnLogScale (digitPMF r n) (digitPMF_support_finite _ _) x := by
  exact digit_gridEntropy_ge_length_div_eight_complexity hr hr0 hr1 n (Real.exp_pos _)
    (Real.exp_le_exp.mpr (by linarith))

lemma digit_entropyOnLogScale_upper {r : ℝ} (hr : IsAlgebraic ℚ r)
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    entropyOnLogScale (digitPMF r n) (digitPMF_support_finite _ _) x ≤
      x + Real.log 4 + complexity r := by
  have h := Bernoulli.digit_entropyOnLogScale_le_support hr0.le hr1 hx n
  have hg := log_inverse_gap_le_complexity hr hr0 hr1
  rw [one_div] at hg
  linarith

lemma coarse_digit_entropy_bound {r : ℝ} (hr : IsAlgebraic ℚ r)
    (hr0 : 0 < r) (hr1 : r < 1) {n : ℕ} (hn : 100 * complexity r ^ 2 ≤ n)
    {x : ℝ} (hx : x ∈ Icc ((n : ℝ) / (32 * complexity r))
      ((n : ℝ) / (32 * complexity r) + Real.log 4)) :
    entropyOnLogScale (digitPMF r n) (digitPMF_support_finite _ _) x ≤
      (n : ℝ) / (16 * complexity r) := by
  have hB := three_le_complexity hr hr0 hr1
  have hB0 := complexity_pos hr hr0 hr1
  have hx0 : 0 ≤ x := (by positivity : 0 ≤ (n : ℝ) / (32 * complexity r)).trans hx.1
  have h := digit_entropyOnLogScale_upper hr hr0 hr1 n hx0
  have hlog : Real.log 4 ≤ 2 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have he : Real.log 4 = 2 * Real.log 2 := by
      have he := Real.log_pow (2 : ℝ) 2
      norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] at he
      exact he
    norm_num at h2
    linarith
  have hgap : complexity r + 2 * Real.log 4 ≤ (n : ℝ) / (32 * complexity r) := by
    apply (le_div_iff₀ (by positivity : 0 < 32 * complexity r)).mpr
    nlinarith
  have he : (n : ℝ) / (16 * complexity r) =
      (n : ℝ) / (32 * complexity r) + (n : ℝ) / (32 * complexity r) := by ring
  rw [he]
  linarith [hx.2]

end LpSelfSimilar.Algebraic
