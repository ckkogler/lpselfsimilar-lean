module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.Tactic

@[expose] public section

/-!
# Fourier transforms of finite real laws

The finite transform is the actual sum of weighted complex phases, with angular
frequency `s`. Expanding its real and imaginary parts gives the squared-norm
identity used to turn phase separation into cancellation. The identity holds for
arbitrary real weights; normalization and nonnegativity enter only where needed.
Using all ordered pairs avoids imposing an order on the atom labels.
-/

open scoped BigOperators

namespace LpSelfSimilar.Fourier

/-- The Fourier transform at angular frequency `s` of the weights `p` at points `z`. -/
noncomputable def finiteTransform {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (s : ℝ) : ℂ :=
  ∑ i, (p i : ℂ) * Complex.exp ((s * z i : ℝ) * Complex.I)

/-- The real part is the weighted cosine sum. -/
theorem finiteTransform_re {ι : Type*} [Fintype ι] (p z : ι → ℝ) (s : ℝ) :
    (finiteTransform p z s).re = ∑ i, p i * Real.cos (s * z i) := by
  simp only [finiteTransform, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]

/-- The imaginary part is the weighted sine sum. -/
theorem finiteTransform_im {ι : Type*} [Fintype ι] (p z : ι → ℝ) (s : ℝ) :
    (finiteTransform p z s).im = ∑ i, p i * Real.sin (s * z i) := by
  simp only [finiteTransform, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]

/-- Squaring the finite Fourier norm gives the cosine of each pairwise phase difference. -/
theorem sq_norm_finiteTransform {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (s : ℝ) :
    ‖finiteTransform p z s‖ ^ 2 =
      ∑ i, ∑ j, p i * p j * Real.cos (s * (z i - z j)) := by
  rw [Complex.sq_norm, Complex.normSq_apply, finiteTransform_re, finiteTransform_im,
    Fintype.sum_mul_sum, Fintype.sum_mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_sub, Real.cos_sub]
  ring

/-- For weights of total mass one, every pairwise phase deficit subtracts from one. -/
theorem sq_norm_finiteTransform_eq_one_sub {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (s : ℝ) (hsum : ∑ i, p i = 1) :
    ‖finiteTransform p z s‖ ^ 2 =
      1 - ∑ i, ∑ j, p i * p j * (1 - Real.cos (s * (z i - z j))) := by
  have htotal : (∑ i, ∑ j, p i * p j) = 1 := by
    rw [← Fintype.sum_mul_sum, hsum, one_mul]
  have hdeficit : (∑ i, ∑ j, p i * p j * (1 - Real.cos (s * (z i - z j)))) =
      (∑ i, ∑ j, p i * p j) - ∑ i, ∑ j, p i * p j * Real.cos (s * (z i - z j)) := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [sq_norm_finiteTransform, hdeficit, htotal]
  ring

/-- The transform of a nonnegative finite probability vector has norm at most one. -/
theorem norm_finiteTransform_le_one {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (s : ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ‖finiteTransform p z s‖ ≤ 1 := by
  calc
    _ ≤ ∑ i, ‖(p i : ℂ) * Complex.exp ((s * z i : ℝ) * Complex.I)‖ :=
      norm_sum_le _ _
    _ = ∑ i, p i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hp i),
        Complex.norm_exp_ofReal_mul_I, mul_one]
    _ = 1 := hsum

end LpSelfSimilar.Fourier
