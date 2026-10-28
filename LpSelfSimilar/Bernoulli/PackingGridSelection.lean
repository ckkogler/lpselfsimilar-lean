module

public import LpSelfSimilar.Bernoulli.PackingGridBudget
public import LpSelfSimilar.Bernoulli.DigitBandGrid

@[expose] public section

/-!
# Deterministic finite selection of attenuating digit bands

The actual entropy and separation assumptions produce a finite translated grid
at each admissible block length. Its attenuation is at least `a_*` and its
candidate count is at most `L/chi`. Removing zero terms retains the same budget.
All scales are selected before any conditional graph labels are sampled.
-/

open MeasureTheory Set
open scoped BigOperators
open LpSelfSimilar.Analysis LpSelfSimilar.Entropy

namespace LpSelfSimilar.Bernoulli

/-- A finite translated candidate grid retains the required attenuation of one block length. -/
theorem exists_packing_grid {θ ρ L : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (n : ℕ) (hn : packingBaseLength (-Real.log θ) (L / ρ) ≤ n)
    (hentropy : ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ x ∈ (digitPMF θ n).support, ∀ y ∈ (digitPMF θ n).support, x ≠ y →
      (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let h := packingGridSpacing (-Real.log θ) n (geometricPhaseLength θ)
    ∃ t : ℝ, packingAttenuation (-Real.log θ) ρ L ≤
      ∑ i ∈ Finset.range (packingGridCandidateCount (-Real.log θ) L n (geometricPhaseLength θ)),
        if h * ((i : ℝ) + t) ∈ Icc ((4 / 25 : ℝ) * ρ * n) (L * n + 4) then
          digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) n (h * ((i : ℝ) + t)) else 0 := by
  classical
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  obtain ⟨t, ht⟩ := exists_digit_grid_budget θ ρ L n hθ0.le hθ1 hρ hρ1 hL hentropy hsep
    (packingFrequencyWidth_pos hJ).le (packingGridSpacing_pos hχ n _)
    (packingGridCandidateCount (-Real.log θ) L n (geometricPhaseLength θ))
    (packingGridCandidateCount_covers hχ L n _)
  exact ⟨t, (packing_grid_budget_with_endpoint hθ0 hθ1 hgap hρ hρ1 hL hC n hn).trans ht⟩

/-- The retained positive grid terms have the required count, scale window and total attenuation. -/
theorem exists_retained_packing_grid {θ ρ L : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hgap : -Real.log θ ≤ 1 / 250) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hL : 3 ≤ L)
    (hC : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2)
    (n : ℕ) (hn : packingBaseLength (-Real.log θ) (L / ρ) ≤ n)
    (hentropy : ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ x ∈ (digitPMF θ n).support, ∀ y ∈ (digitPMF θ n).support, x ≠ y →
      (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    let h := packingGridSpacing (-Real.log θ) n (geometricPhaseLength θ)
    ∃ (t : ℝ) (I : Finset ℕ), (I.card : ℝ) ≤ L / (-Real.log θ) ∧
      (∀ i ∈ I, h * ((i : ℝ) + t) ∈ Icc ((4 / 25 : ℝ) * ρ * n) (L * n + 4) ∧
        0 < digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) n (h * ((i : ℝ) + t))) ∧
      packingAttenuation (-Real.log θ) ρ L ≤
        ∑ i ∈ I, digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) n (h * ((i : ℝ) + t)) := by
  classical
  have hχ : 0 < -Real.log θ := neg_pos.mpr (Real.log_neg hθ0 hθ1)
  have hJ := three_le_separation_entropy_ratio hρ hρ1 hL
  obtain ⟨t, ht⟩ := exists_packing_grid hθ0 hθ1 hgap hρ hρ1 hL hC n hn hentropy hsep
  let h := packingGridSpacing (-Real.log θ) n (geometricPhaseLength θ)
  let N := packingGridCandidateCount (-Real.log θ) L n (geometricPhaseLength θ)
  let g : ℕ → ℝ := fun i ↦
    digitGridAttenuation θ (packingFrequencyWidth (L / ρ)) n (h * ((i : ℝ) + t))
  let P : ℕ → Prop := fun i ↦ h * ((i : ℝ) + t) ∈ Icc ((4 / 25 : ℝ) * ρ * n) (L * n + 4)
  let I := (Finset.range N).filter (fun i ↦ P i ∧ 0 < g i)
  have hsum : (∑ i ∈ I, g i) = ∑ i ∈ Finset.range N, if P i then g i else 0 := by
    rw [show I = (Finset.range N).filter (fun i ↦ P i ∧ 0 < g i) from rfl, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hp : P i
    · by_cases hg : 0 < g i
      · simp [hp, hg]
      · have hz : g i = 0 := le_antisymm (le_of_not_gt hg)
          (digitGridAttenuation_mem_Icc θ (packingFrequencyWidth_pos hJ).le n _).1
        simp [hp, hz]
    · simp [hp]
  refine ⟨t, I, ?_, ?_, ?_⟩
  · have hc : I.card ≤ N := by
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hc' : (I.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hc
    exact hc'.trans (packingGridCandidateCount_le hχ hgap hρ hρ1 hL n _ hn)
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · change packingAttenuation (-Real.log θ) ρ L ≤ ∑ i ∈ I, g i
    rw [hsum]
    exact ht

end LpSelfSimilar.Bernoulli
