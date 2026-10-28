module

public import LpSelfSimilar.Analysis.QuadraticGeometricSum
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# Integrating decay indexed by a measurable geometric count

The count fibers partition the half-line. If the fiber with index n lies below
A*N^n, its volume is at most A*N^n. This absorbs the geometric interval length
into the attenuation, retaining the zero-index fiber and proving integrability
before using the countable integral identity.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar.Analysis

/-- A measurable geometric count converts quadratic attenuation into a finite scale integral. -/
theorem integrableOn_and_integral_le_of_geometric_count
    {f : ℝ → ℝ} {c : ℝ → ℕ} {A N B α a : ℝ}
    (hA : 0 < A) (hN : 0 < N) (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hc : Measurable c) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hscale : ∀ x, a ≤ x → x < A * N ^ c x)
    (hbound : ∀ x, a ≤ x →
      f x ≤ B * ((c x : ℝ) + 1) ^ 2 * Real.exp (-α * c x))
    (hratio : N * Real.exp (-α) ≤ 1 / 15) :
    IntegrableOn f (Ici a) volume ∧ (∫ x in Ici a, f x) ≤ 2 * B * A := by
  let s : ℕ → Set ℝ := fun n => Ici a ∩ {x | c x = n}
  let C : ℕ → ℝ := fun n => B * ((n : ℝ) + 1) ^ 2 * Real.exp (-α * n)
  have hC (n : ℕ) : 0 ≤ C n := by dsimp [C]; positivity
  have hm (n : ℕ) : MeasurableSet (s n) :=
    measurableSet_Ici.inter (hc (measurableSet_singleton n))
  have hd : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hi hj
    exact hij (hi.2.symm.trans hj.2)
  have hu : (⋃ n, s n) = Ici a := by ext x; simp [s]
  have hsub (n : ℕ) : s n ⊆ Ico 0 (A * N ^ n) := by
    intro x hx
    refine ⟨ha.trans hx.1, ?_⟩
    have he : c x = n := hx.2
    simpa only [he] using hscale x hx.1
  have hvupper (n : ℕ) : volume (Ico 0 (A * N ^ n)) < ∞ := by
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_lt_top
  have hfinite (n : ℕ) : volume (s n) < ∞ :=
    (measure_mono (hsub n)).trans_lt (hvupper n)
  have hvol (n : ℕ) : volume.real (s n) ≤ A * N ^ n := by
    have hh := ENNReal.toReal_mono (hvupper n).ne
      (measure_mono (hsub n))
    change volume.real (s n) ≤ volume.real (Ico 0 (A * N ^ n)) at hh
    rw [Real.volume_real_Ico_of_le (by positivity), sub_zero] at hh
    exact hh
  have hnorm (n : ℕ) (x : ℝ) (hx : x ∈ s n) : ‖f x‖ ≤ C n := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    have he : c x = n := hx.2
    simpa only [C, he] using hbound x hx.1
  have hi (n : ℕ) : IntegrableOn f (s n) volume := by
    apply (integrableOn_const (hfinite n).ne :
      IntegrableOn (fun _ : ℝ => C n) (s n) volume).mono' hf.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (hm n)] with x hx
    exact hnorm n x hx
  have hb (n : ℕ) : (∫ x in s n, ‖f x‖) ≤
      (B * A) * (((n : ℝ) + 1) ^ 2 * (N * Real.exp (-α)) ^ n) := by
    calc
      _ ≤ C n * volume.real (s n) := by
        have hh := norm_setIntegral_le_of_norm_le_const (f := fun x => ‖f x‖)
          (hfinite n) (fun x hx => by simpa only [norm_norm] using hnorm n x hx)
        exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hh)
      _ ≤ C n * (A * N ^ n) := mul_le_mul_of_nonneg_left (hvol n) (hC n)
      _ = _ := by
        have he : Real.exp (-α * n) = Real.exp (-α) ^ n := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        dsimp only [C]
        rw [he, mul_pow]
        ring
  have hq : 0 ≤ N * Real.exp (-α) := by positivity
  have hs := (summable_quadratic_geometric_of_le_one_fifteenth hq hratio).mul_left (B * A)
  have hsi : Summable (fun n : ℕ => ∫ x in s n, ‖f x‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _)) hb hs
  have hfi : IntegrableOn f (⋃ n, s n) volume :=
    integrableOn_iUnion_of_summable_integral_norm hi hsi
  refine ⟨by rwa [hu] at hfi, ?_⟩
  have hfnorm : (fun n : ℕ => ∫ x in s n, f x) = (fun n : ℕ => ∫ x in s n, ‖f x‖) := by
    simp only [Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
  calc
    _ = ∑' n, ∫ x in s n, f x := by rw [← hu]; exact integral_iUnion hm hd hfi
    _ = ∑' n, ∫ x in s n, ‖f x‖ := congrArg tsum hfnorm
    _ ≤ ∑' n : ℕ, (B * A) * (((n : ℝ) + 1) ^ 2 * (N * Real.exp (-α)) ^ n) :=
      hsi.tsum_le_tsum hb hs
    _ = (B * A) * ∑' n : ℕ, ((n : ℝ) + 1) ^ 2 * (N * Real.exp (-α)) ^ n :=
      tsum_mul_left
    _ ≤ (B * A) * 2 := mul_le_mul_of_nonneg_left
      (tsum_quadratic_geometric_lt_two hq hratio).le (mul_nonneg hB hA.le)
    _ = 2 * B * A := by ring

end LpSelfSimilar.Analysis
