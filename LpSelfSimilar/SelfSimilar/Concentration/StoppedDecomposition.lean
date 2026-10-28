module

public import LpSelfSimilar.SelfSimilar.Concentration.Definitions

@[expose] public section

/-!
# Finite concentration stopping and its exact measure decomposition

At each node stop if its interval is concentrated, and otherwise read one
more digit. A finite horizon leaves the current affine map at the final
level. Averaging over all binary words, including unused suffixes after a
stop, preserves the exact stationary measure decomposition at every depth.
-/

open MeasureTheory Set
open LpSelfSimilar.Geometry
open scoped ENNReal Classical

namespace LpSelfSimilar.SelfSimilar.Concentration

/-- Uniform binary words of depth n have total product probability one. -/
theorem uniform_word_weight_sum (n : ℕ) :
    (∑ _w : Word Bool n, (1 / 2 : ℝ≥0∞) ^ n) = 1 := by
  induction n with
  | zero => change (∑ _w : PUnit, (1 / 2 : ℝ≥0∞) ^ 0) = 1; simp
  | succ n ih =>
    change (∑ _w : Bool × Word Bool n, (1 / 2 : ℝ≥0∞) ^ (n + 1)) = 1
    rw [Fintype.sum_prod_type]
    simp_rw [pow_succ, ← Finset.sum_mul, ih]
    norm_num [Fintype.sum_bool, ENNReal.mul_inv_cancel]

/-- Stop at the first concentrated interval or at the available finite horizon. -/
noncomputable def stoppedMap {θ : ℝ} (hθ : 0 < θ) (E : Set ℝ) (r : ℝ) :
    (n : ℕ) → PositiveAffine → Word Bool n → PositiveAffine
  | 0, q, _ => q
  | n + 1, q, w => if IsConcentrated E r q then q else
      stoppedMap hθ E r n (q.comp (digitMap hθ w.1)) w.2

/-- The finite concentration-stopped decomposition preserves the actual stationary measure. -/
theorem stopped_decomposition {θ : ℝ} (hθ : 0 < θ) {μ : Measure ℝ}
    (hμ : IsStationary hθ μ) (E : Set ℝ) (r : ℝ) (n : ℕ) (q : PositiveAffine)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (∑ w : Word Bool n, (1 / 2 : ℝ≥0∞) ^ n *
      μ ((stoppedMap hθ E r n q w) ⁻¹' A)) = μ (q ⁻¹' A) := by
  classical
  induction n generalizing q with
  | zero =>
    change (∑ _w : PUnit, (1 / 2 : ℝ≥0∞) ^ 0 * μ (q ⁻¹' A)) = _
    simp
  | succ n ih =>
    change (∑ w : Bool × Word Bool n, (1 / 2 : ℝ≥0∞) ^ (n + 1) *
      μ ((stoppedMap hθ E r (n + 1) q w) ⁻¹' A)) = _
    by_cases hq : IsConcentrated E r q
    · simp only [stoppedMap, hq, ↓reduceIte]
      rw [← Finset.sum_mul]
      change (∑ _w : Word Bool (n + 1), (1 / 2 : ℝ≥0∞) ^ (n + 1)) * μ (q ⁻¹' A) = _
      rw [uniform_word_weight_sum, one_mul]
    · rw [Fintype.sum_prod_type]
      simp only [stoppedMap, hq, ↓reduceIte]
      have hw (b : Bool) : (∑ w : Word Bool n,
          (1 / 2 : ℝ≥0∞) ^ (n + 1) *
            μ ((stoppedMap hθ E r n (q.comp (digitMap hθ b)) w) ⁻¹' A)) =
          (1 / 2 : ℝ≥0∞) * μ ((q.comp (digitMap hθ b)) ⁻¹' A) := by
        rw [pow_succ]
        calc
          _ = (1 / 2 : ℝ≥0∞) * (∑ w : Word Bool n, (1 / 2 : ℝ≥0∞) ^ n *
              μ ((stoppedMap hθ E r n (q.comp (digitMap hθ b)) w) ⁻¹' A)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro w hw
            ring
          _ = _ := by rw [ih]
      simp_rw [hw]
      rw [stationary_apply hμ (hA.preimage q.measurable)]
      apply Finset.sum_congr rfl
      intro b hb
      congr 2
      ext x
      simp only [mem_preimage, PositiveAffine.comp_apply]

end LpSelfSimilar.SelfSimilar.Concentration
