module

public import LpSelfSimilar.Bernoulli.BlockPlacement

@[expose] public section

/-!
Separated logarithmic windows for different block lengths. The explicit bounds
1/(200B) and 400B² turn the ceiling arithmetic into disjointness of digit sets.
-/

open Set

namespace LpSelfSimilar.Bernoulli

lemma blockStart_window_of_source_bounds {χ B T v : ℝ} (hχ : 0 < χ) (hB : 0 < B)
    (hsmall : χ ≤ 1 / (200 * B)) {n j : ℕ}
    (hv : v ∈ Icc ((n : ℝ) / (100 * B)) (2 * B * n)) (hvT : v ≤ T)
    (hj : j ∈ Finset.Ico (blockStart χ T v) (blockStart χ T v + n)) :
    (n : ℝ) / (200 * B) < T - (j : ℝ) * χ ∧ T - (j : ℝ) * χ ≤ 2 * B * n := by
  have hw := blockStart_digit_window hχ hvT hj
  have hmul := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have he : (n : ℝ) / (100 * B) = 2 * ((n : ℝ) / (200 * B)) := by ring
  constructor
  · have hlo : (n : ℝ) / (200 * B) ≤ v - (n : ℝ) * χ := by
      rw [mul_one_div] at hmul
      linarith [hv.1]
    exact hlo.trans_lt hw.1
  · exact hw.2.trans hv.2

/-- Lengths with ratio at least `400B²` occupy disjoint digit windows. -/
theorem blockStart_disjoint_of_length_separation {χ B T u v : ℝ}
    (hχ : 0 < χ) (hB : 0 < B) (hsmall : χ ≤ 1 / (200 * B)) {n m : ℕ}
    (hsep : 400 * B ^ 2 * (n : ℝ) ≤ m)
    (hu : u ∈ Icc ((n : ℝ) / (100 * B)) (2 * B * n)) (huT : u ≤ T)
    (hv : v ∈ Icc ((m : ℝ) / (100 * B)) (2 * B * m)) (hvT : v ≤ T) :
    Disjoint (Finset.Ico (blockStart χ T u) (blockStart χ T u + n))
      (Finset.Ico (blockStart χ T v) (blockStart χ T v + m)) := by
  have hgap : 2 * B * (n : ℝ) ≤ (m : ℝ) / (200 * B) := by
    apply (le_div_iff₀ (by positivity : 0 < 200 * B)).mpr
    nlinarith
  apply Finset.disjoint_left.mpr
  intro j hju hjv
  have hw₁ := blockStart_window_of_source_bounds hχ hB hsmall hu huT hju
  have hw₂ := blockStart_window_of_source_bounds hχ hB hsmall hv hvT hjv
  linarith [hw₁.2, hw₂.1]

end LpSelfSimilar.Bernoulli
