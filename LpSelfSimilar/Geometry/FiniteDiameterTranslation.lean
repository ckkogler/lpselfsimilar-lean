module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic

@[expose] public section

/-!
# Translating a finite real support into an interval

Choosing a smallest atom turns a diameter bound into support in `[0,D]`.
The empty support is handled separately. The probability-vector formulation
ignores exactly the zero coordinates and does not change their weights.
-/

namespace LpSelfSimilar.Geometry

/-- Any finite real configuration of diameter at most `D` translates into `[0,D]`. -/
theorem exists_translation_of_finite_diameter {ι : Type*} (s : Finset ι)
    (z : ι → ℝ) {D : ℝ}
    (hdiam : ∀ i ∈ s, ∀ j ∈ s, |z i - z j| ≤ D) :
    ∃ b : ℝ, ∀ i ∈ s, 0 ≤ z i - b ∧ z i - b ≤ D := by
  classical
  by_cases hne : s.Nonempty
  · obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image s z hne
    refine ⟨z j, fun i hi ↦ ⟨sub_nonneg.mpr (hmin i hi), ?_⟩⟩
    exact (le_abs_self _).trans (hdiam i hi j hj)
  · refine ⟨0, ?_⟩
    intro i hi
    exact False.elim (hne ⟨i, hi⟩)

/-- A finite weighted configuration can be translated using only its nonzero atoms. -/
theorem exists_translation_of_nonzero_diameter {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) {D : ℝ}
    (hdiam : ∀ i, p i ≠ 0 → ∀ j, p j ≠ 0 → |z i - z j| ≤ D) :
    ∃ b : ℝ, ∀ i, p i ≠ 0 → 0 ≤ z i - b ∧ z i - b ≤ D := by
  classical
  let s := Finset.univ.filter (fun i ↦ p i ≠ 0)
  have hs (i : ι) : i ∈ s ↔ p i ≠ 0 := by simp [s]
  obtain ⟨b, hb⟩ := exists_translation_of_finite_diameter s z
    (fun i hi j hj ↦ hdiam i ((hs i).mp hi) j ((hs j).mp hj))
  exact ⟨b, fun i hi ↦ hb i ((hs i).mpr hi)⟩

end LpSelfSimilar.Geometry
