module

public import LpSelfSimilar.Gaussian.HigherDetail
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-!
Taylor expansion in Gaussian variance on a strictly positive compact interval.
All derivative identifications are local to positive variance; no regularity at
variance zero is assumed. This finite-interval formula avoids improper boundary
terms when comparing higher and ordinary detail.
-/

open MeasureTheory MeasureTheory.Measure Real Filter Set
open scoped Topology

namespace LpSelfSimilar.Gaussian

lemma contDiffOn_higherSmooth_variance (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n k : ℕ) (x : ℝ) : ContDiffOn ℝ n (fun y ↦ higherSmooth μ k y x) (Ioi 0) := by
  induction n generalizing k with
  | zero =>
    apply contDiffOn_zero.mpr
    exact fun y hy ↦ (hasDerivAt_higherSmooth_variance μ k hy x).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun y hy ↦ (hasDerivAt_higherSmooth_variance μ k hy x).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    apply (ih (k + 1)).congr
    intro y hy
    exact (hasDerivAt_higherSmooth_variance μ k hy x).deriv

lemma iteratedDeriv_higherSmooth_variance (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    iteratedDeriv n (fun z ↦ higherSmooth μ k z x) y = higherSmooth μ (k + n) y x := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv n (fun z ↦ higherSmooth μ k z x) =ᶠ[𝓝 y]
        (fun z ↦ higherSmooth μ (k + n) z x) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact ih hz
    rw [he.deriv_eq, (hasDerivAt_higherSmooth_variance μ (k + n) hy x).deriv]
    congr 1

/-- Finite Taylor expansion of the first smoothed variance derivative about
an upper variance. The entire interpolation segment has positive variance. -/
theorem firstSmooth_taylor_variance (μ : Measure ℝ) [IsFiniteMeasure μ]
    (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (x : ℝ) :
    firstSmooth μ a x =
      (∑ j ∈ Finset.range (n + 1), (a - b) ^ j / (j.factorial : ℝ) * higherSmooth μ (j + 1) b x) +
      (a - b) ^ (n + 1) / (n.factorial : ℝ) *
        ∫ t in (0 : ℝ)..1, (1 - t) ^ n * higherSmooth μ (n + 2) (b + t * (a - b)) x := by
  have hb := ha.trans_le hab
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < b + t * (a - b) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr ht.2)]
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := fun y ↦ higherSmooth μ 1 y x) (x := b) (y := a - b) (n := n)
    (fun t ht ↦ (contDiffOn_higherSmooth_variance μ (n + 1) 1 x).contDiffAt
      (Ioi_mem_nhds (by simpa only [smul_eq_mul] using hpos t ht)))
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, add_sub_cancel,
    higherSmooth_one μ ha] at ht
  have hsum : (∑ j ∈ Finset.range (n + 1), (j.factorial : ℝ)⁻¹ *
      ((a - b) ^ j * iteratedDeriv j (fun y ↦ higherSmooth μ 1 y x) b)) =
      ∑ j ∈ Finset.range (n + 1), (a - b) ^ j / (j.factorial : ℝ) * higherSmooth μ (j + 1) b x := by
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedDeriv_higherSmooth_variance μ j 1 hb x, Nat.add_comm 1 j]
    ring
  rw [hsum] at ht
  have he : (∫ t in (0 : ℝ)..1, (1 - t) ^ n *
      ((a - b) ^ (n + 1) * iteratedDeriv (n + 1) (fun y ↦ higherSmooth μ 1 y x) (b + t * (a - b)))) =
      (a - b) ^ (n + 1) * ∫ t in (0 : ℝ)..1,
        (1 - t) ^ n * higherSmooth μ (n + 2) (b + t * (a - b)) x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    dsimp only
    rw [iteratedDeriv_higherSmooth_variance μ (n + 1) 1 (hpos t ht) x]
    have hn : 1 + (n + 1) = n + 2 := by omega
    rw [hn]
    ring
  rw [he] at ht
  convert ht using 1 <;> try rfl
  ring

end LpSelfSimilar.Gaussian
