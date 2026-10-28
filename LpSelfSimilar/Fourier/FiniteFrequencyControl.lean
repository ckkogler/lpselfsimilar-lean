module

public import LpSelfSimilar.Fourier.FiniteAffine
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Frequency control by the first absolute moment

Complex phases are one-Lipschitz in their real angle. Consequently a finite
probability law supported in `[-D,D]` has a `D`-Lipschitz Fourier transform.
Evenness of its norm extends control near frequency `1/r` to both sides of the
band `abs(abs(xi)-1) <= epsilon`, retaining the exact loss `52*epsilon`.
-/

open scoped BigOperators

namespace LpSelfSimilar.Fourier

/-- Unit complex phases are one-Lipschitz in their angular argument. -/
theorem norm_phase_sub_phase_le (x y : ℝ) :
    ‖Complex.exp ((x : ℝ) * Complex.I) - Complex.exp ((y : ℝ) * Complex.I)‖ ≤ |x - y| := by
  have he : Complex.exp ((x : ℝ) * Complex.I) - Complex.exp ((y : ℝ) * Complex.I) =
      Complex.exp ((y : ℝ) * Complex.I) *
        (Complex.exp ((x - y : ℝ) * Complex.I) - 1) := by
    rw [show (x : ℂ) * Complex.I = (y : ℂ) * Complex.I +
      ((x - y : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_add]
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [mul_comm, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

/-- The first absolute moment controls variation of a finite nonnegative transform. -/
theorem norm_finiteTransform_sub_le_moment {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (s t : ℝ) :
    ‖finiteTransform p z s - finiteTransform p z t‖ ≤
      (∑ i, p i * |z i|) * |s - t| := by
  have he : finiteTransform p z s - finiteTransform p z t =
      ∑ i, (p i : ℂ) * (Complex.exp ((s * z i : ℝ) * Complex.I) -
        Complex.exp ((t * z i : ℝ) * Complex.I)) := by
    simp only [finiteTransform, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, ‖(p i : ℂ) * (Complex.exp ((s * z i : ℝ) * Complex.I) -
        Complex.exp ((t * z i : ℝ) * Complex.I))‖ := norm_sum_le _ _
    _ ≤ ∑ i, p i * (|s - t| * |z i|) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp i)]
      apply mul_le_mul_of_nonneg_left _ (hp i)
      simpa only [← sub_mul, abs_mul] using norm_phase_sub_phase_le (s * z i) (t * z i)
    _ = (∑ i, p i * |z i|) * |s - t| := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Bounded nonzero atoms give a uniform frequency Lipschitz constant for a probability law. -/
theorem norm_finiteTransform_sub_le_of_bounded {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {D : ℝ} (hbound : ∀ i, p i ≠ 0 → |z i| ≤ D) (s t : ℝ) :
    ‖finiteTransform p z s - finiteTransform p z t‖ ≤ D * |s - t| := by
  have hm : (∑ i, p i * |z i|) ≤ D := by
    calc
      _ ≤ ∑ i, p i * D := Finset.sum_le_sum fun i hi ↦ by
        by_cases hpi : p i = 0
        · simp [hpi]
        · exact mul_le_mul_of_nonneg_left (hbound i hpi) (hp i)
      _ = D := by rw [← Finset.sum_mul, hsum, one_mul]
  exact (norm_finiteTransform_sub_le_moment p z hp s t).trans
    (mul_le_mul_of_nonneg_right hm (abs_nonneg _))

/-- The same support bound controls variation of the Fourier norm. -/
theorem abs_norm_finiteTransform_sub_norm_le {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {D : ℝ} (hbound : ∀ i, p i ≠ 0 → |z i| ≤ D) (s t : ℝ) :
    |‖finiteTransform p z s‖ - ‖finiteTransform p z t‖| ≤ D * |s - t| :=
  (abs_norm_sub_norm_le _ _).trans (norm_finiteTransform_sub_le_of_bounded p z hp hsum hbound s t)

/-- On the two-sided frequency band, support width `52*r` costs at most `52*epsilon`. -/
theorem norm_finiteTransform_frequency_band_le {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    {r ξ ε : ℝ} (hr : 0 < r) (hbound : ∀ i, p i ≠ 0 → |z i| ≤ 52 * r)
    (hξ : abs (|ξ| - 1) ≤ ε) :
    ‖finiteTransform p z (ξ / r)‖ ≤ ‖finiteTransform p z (1 / r)‖ + 52 * ε := by
  have he : ‖finiteTransform p z (ξ / r)‖ = ‖finiteTransform p z (|ξ| / r)‖ := by
    rw [← norm_finiteTransform_abs p z (ξ / r), abs_div, abs_of_pos hr]
  have h := abs_norm_finiteTransform_sub_norm_le p z hp hsum hbound (|ξ| / r) (1 / r)
  have hfactor : (52 * r) * abs (|ξ| / r - 1 / r) = 52 * abs (|ξ| - 1) := by
    rw [← sub_div, abs_div, abs_of_pos hr]
    field_simp
  rw [hfactor] at h
  rw [he]
  have hu := (abs_le.mp h).2
  linarith

end LpSelfSimilar.Fourier
