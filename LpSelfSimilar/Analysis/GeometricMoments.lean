module

public import LpSelfSimilar.Analysis.MeasureExpansion
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! A geometric tail estimate implies a finite moment. -/

open MeasureTheory Set
open scoped ENNReal

namespace LpSelfSimilar

lemma lintegral_rpow_lt_top_of_geometric_tails {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] (f : X → ℝ)
    {L A β t : ℝ} (hL : 0 < L) (hA : 1 < A) (ht : 0 ≤ t)
    (hratio : β * A ^ t < 1)
    (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n))
    (hcover : ∀ n x, L * A ^ n ≤ f x → x ∈ S n)
    (hmass : ∀ n, ν (S n) ≤ ENNReal.ofReal β ^ n * ν univ) :
    ∫⁻ x, ENNReal.ofReal (f x) ^ t ∂ν < ∞ := by
  classical
  have hA0 : 0 < A := lt_trans zero_lt_one hA
  let K : ℝ≥0∞ := ENNReal.ofReal ((L * A) ^ t)
  let q : ℝ≥0∞ := ENNReal.ofReal (A ^ t)
  let F : ℕ → X → ℝ≥0∞ := fun n ↦ (S n).indicator (fun _ ↦ K * q ^ n)
  have hF : ∀ n, Measurable (F n) := fun n ↦ measurable_const.indicator (hS n)
  have hpoint (x : X) : ENNReal.ofReal (f x) ^ t ≤
      ENNReal.ofReal L ^ t + ∑' n, F n x := by
    by_cases hx : f x ≤ L
    · exact (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hx) ht).trans (le_self_add)
    · have hxL : L ≤ f x := (lt_of_not_ge hx).le
      obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near ((le_div_iff₀ hL).2 (by simpa using hxL)) hA
      have hxS : x ∈ S n := hcover n x (by nlinarith [(le_div_iff₀ hL).1 hn])
      have hxupper : f x ≤ L * A ^ (n + 1) := by
        have := (div_lt_iff₀ hL).1 hn'
        nlinarith
      have hweight : ENNReal.ofReal (L * A ^ (n + 1)) ^ t = K * q ^ n := by
        rw [ENNReal.ofReal_rpow_of_pos (by positivity), pow_succ,
          show L * (A ^ n * A) = (L * A) * A ^ n by ring,
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_natCast_mul hA0.le, mul_comm (n : ℝ) t,
          Real.rpow_mul_natCast hA0.le, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow (by positivity)]
      calc
        ENNReal.ofReal (f x) ^ t ≤ ENNReal.ofReal (L * A ^ (n + 1)) ^ t :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hxupper) ht
        _ = F n x := by rw [hweight]; simp [F, hxS]
        _ ≤ ∑' k, F k x := ENNReal.le_tsum (f := fun k => F k x) n
        _ ≤ ENNReal.ofReal L ^ t + ∑' k, F k x := le_add_self
  have hterm (n : ℕ) : ∫⁻ x, F n x ∂ν ≤
      K * ν univ * (q * ENNReal.ofReal β) ^ n := by
    rw [show (∫⁻ x, F n x ∂ν) = K * q ^ n * ν (S n) by
      exact lintegral_indicator_const (hS n) _]
    calc
      K * q ^ n * ν (S n) ≤ K * q ^ n * (ENNReal.ofReal β ^ n * ν univ) := by
        gcongr
        exact hmass n
      _ = K * ν univ * (q * ENNReal.ofReal β) ^ n := by rw [mul_pow]; ac_rfl
  have hq : q * ENNReal.ofReal β < 1 := by
    dsimp [q]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hA0.le t), ENNReal.ofReal_lt_one]
    simpa only [mul_comm] using hratio
  have hsum : (∑' n, ∫⁻ x, F n x ∂ν) < ∞ := by
    refine (ENNReal.tsum_le_tsum hterm).trans_lt ?_
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν univ))
      (tsum_geometric_lt_top.mpr hq)
  calc
    ∫⁻ x, ENNReal.ofReal (f x) ^ t ∂ν ≤
        ∫⁻ x, ENNReal.ofReal L ^ t + ∑' n, F n x ∂ν := lintegral_mono hpoint
    _ = ENNReal.ofReal L ^ t * ν univ + ∑' n, ∫⁻ x, F n x ∂ν := by
      rw [lintegral_add_left measurable_const, lintegral_const, lintegral_tsum]
      exact fun n ↦ (hF n).aemeasurable
    _ < ∞ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg ht ENNReal.ofReal_ne_top) (measure_lt_top ν univ), hsum⟩

end LpSelfSimilar
