module

public import LpSelfSimilar.Bernoulli.PackingParameters

@[expose] public section

/-!
# A finite candidate grid with the required block count

The candidate count is the natural ceiling of the upper scale endpoint divided
by the padded grid spacing. It covers the entire integration interval. The large
starting length and the logarithmic gap bound make even this unfiltered count
at most `L/chi`; filtering positive attenuations can only reduce it.
-/

open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- Padded distance between successive dyadic scale samples. -/
noncomputable def packingGridSpacing (χ : ℝ) (n K : ℕ) : ℝ :=
  ((n : ℝ) + K + 2) * (χ / Real.log 2)

/-- A finite candidate range that covers the upper integration endpoint. -/
noncomputable def packingGridCandidateCount (χ L : ℝ) (n K : ℕ) : ℕ :=
  ⌈(L * n + 4) / packingGridSpacing χ n K⌉₊

/-- The padded spacing is positive for every natural block and phase length. -/
theorem packingGridSpacing_pos {χ : ℝ} (hχ : 0 < χ) (n K : ℕ) :
    0 < packingGridSpacing χ n K := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold packingGridSpacing
  positivity

/-- The finite candidate grid covers the upper endpoint, without losing a ceiling term. -/
theorem packingGridCandidateCount_covers {χ : ℝ} (hχ : 0 < χ) (L : ℝ) (n K : ℕ) :
    L * n + 4 ≤ packingGridSpacing χ n K * (packingGridCandidateCount χ L n K : ℝ) := by
  have hc : (L * n + 4) / packingGridSpacing χ n K ≤
      (packingGridCandidateCount χ L n K : ℝ) := Nat.le_ceil _
  have h := (div_le_iff₀ (packingGridSpacing_pos hχ n K)).mp hc
  simpa only [mul_comm] using h

/-- Even the whole candidate grid has at most `L/chi` samples at every allowed block length. -/
theorem packingGridCandidateCount_le {χ ρ L : ℝ} (hχ : 0 < χ) (hχ1 : χ ≤ 1 / 250)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L) (n K : ℕ)
    (hn : packingBaseLength χ (L / ρ) ≤ n) :
    (packingGridCandidateCount χ L n K : ℝ) ≤ L / χ := by
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  have ht := six_lt_packingLogScale hJ
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlu : Real.log 2 < (7 / 10 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hbase : 1000000 * (L / ρ) * packingLogScale (L / ρ) / χ ≤ (n : ℝ) :=
    (packingBaseLength_lower_bound _ _).trans (by exact_mod_cast hn)
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hbase
  have hnχ := (div_le_iff₀ hχ).mp hbase
  have hnχlarge : 4 * Real.log 2 ≤ (n : ℝ) * χ := by nlinarith
  have htail : 4 * Real.log 2 / ((n : ℝ) * χ) ≤ 1 := by
    apply (div_le_iff₀ (mul_pos hn0 hχ)).mpr
    simpa only [one_mul] using hnχlarge
  have hspacing : (n : ℝ) * (χ / Real.log 2) ≤ packingGridSpacing χ n K := by
    unfold packingGridSpacing
    apply mul_le_mul_of_nonneg_right (by have hK := Nat.cast_nonneg (α := ℝ) K; linarith) (by positivity)
  have hh := packingGridSpacing_pos hχ n K
  have hceil : (packingGridCandidateCount χ L n K : ℝ) <
      (L * n + 4) / packingGridSpacing χ n K + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hquot : (L * n + 4) / packingGridSpacing χ n K ≤
      L * Real.log 2 / χ + 1 := by
    calc
      _ ≤ (L * n + 4) / ((n : ℝ) * (χ / Real.log 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hspacing
      _ = L * Real.log 2 / χ + 4 * Real.log 2 / ((n : ℝ) * χ) := by field_simp
      _ ≤ _ := by linarith [htail]
  have hfinal : L * Real.log 2 / χ + 2 ≤ L / χ := by
    apply (le_div_iff₀ hχ).mpr
    rw [add_mul, div_mul_cancel₀ _ hχ.ne']
    nlinarith
  linarith

end LpSelfSimilar.Bernoulli
