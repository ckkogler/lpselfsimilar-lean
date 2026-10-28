module

public import LpSelfSimilar.Geometry.Similarity

@[expose] public section

/-!
Finite systems of contracting Euclidean similarities and their stationary
measures. Nonnegative weights are represented by `ℝ≥0`; zero weights are
allowed throughout. Stationarity is equality with the finite sum of pushforwards.
-/

open MeasureTheory Metric Set
open scoped ENNReal NNReal BigOperators

namespace LpSelfSimilar.SelfSimilar

/-- The maps and weights appearing in Theorem 1.1. -/
structure System (d : ℕ) (ι : Type*) [Fintype ι] where
  map : ι → Similarity d
  contracting : ∀ i, (map i).ratio < 1
  weight : ι → ℝ≥0
  weight_sum : ∑ i, weight i = 1

namespace System

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- The stationarity equation, with the usual pushforward of measures. -/
def IsStationary (S : System d ι) (ν : Measure (Space d)) : Prop :=
  ν = ∑ i, (S.weight i : ℝ≥0∞) • ν.map (S.map i)

lemma weight_sum_ennreal (S : System d ι) : ∑ i, (S.weight i : ℝ≥0∞) = 1 := by
  exact_mod_cast S.weight_sum

lemma stationary_apply (S : System d ι) {ν : Measure (Space d)}
    (hν : S.IsStationary ν) {E : Set (Space d)} (hE : MeasurableSet E) :
    ν E = ∑ i, (S.weight i : ℝ≥0∞) * ν ((S.map i) ⁻¹' E) := by
  conv_lhs => rw [hν]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  congr 1
  ext i
  rw [Measure.map_apply (S.map i).measurable hE]

/-- A common inverse-image containment transfers through a stationary convex combination. -/
lemma measure_le_of_preimages_subset (S : System d ι) {ν : Measure (Space d)}
    (hν : S.IsStationary ν) {E F : Set (Space d)} (hE : MeasurableSet E)
    (hsub : ∀ i, (S.map i) ⁻¹' E ⊆ F) : ν E ≤ ν F := by
  rw [S.stationary_apply hν hE]
  calc
    ∑ i, (S.weight i : ℝ≥0∞) * ν ((S.map i) ⁻¹' E) ≤
        ∑ i, (S.weight i : ℝ≥0∞) * ν F := by
      exact Finset.sum_le_sum fun i _ ↦ mul_le_mul' le_rfl (measure_mono (hsub i))
    _ = ν F := by rw [← Finset.sum_mul, S.weight_sum_ennreal, one_mul]

/-- Finiteness gives a uniform strictly contracting upper ratio and a bounded displacement. -/
lemma exists_uniform_bounds (S : System d ι) [Nonempty ι] :
    ∃ c M : ℝ, 0 < c ∧ c < 1 ∧ 0 ≤ M ∧
      (∀ i, (S.map i).ratio ≤ c) ∧ (∀ i, ‖(S.map i).shift‖ ≤ M) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i ↦ (S.map i).ratio) Finset.univ_nonempty
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j ↦ ‖(S.map j).shift‖) Finset.univ_nonempty
  exact ⟨(S.map i).ratio, ‖(S.map j).shift‖, (S.map i).ratio_pos,
    S.contracting i, norm_nonneg _, fun k ↦ hi k (Finset.mem_univ k),
    fun k ↦ hj k (Finset.mem_univ k)⟩

/-- The smallest ratio is positive even when some of the weights vanish. -/
lemma exists_min_ratio (S : System d ι) [Nonempty ι] :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∀ i, a ≤ (S.map i).ratio := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun i ↦ (S.map i).ratio) Finset.univ_nonempty
  exact ⟨(S.map i).ratio, (S.map i).ratio_pos, S.contracting i,
    fun k ↦ hi k (Finset.mem_univ k)⟩

end System
end LpSelfSimilar.SelfSimilar
