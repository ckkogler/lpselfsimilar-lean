module

public import LpSelfSimilar.Fourier.FiniteTransform

@[expose] public section

/-!
# Scaling, translation and reflection of finite Fourier transforms

Scaling atom locations scales angular frequency. Translation multiplies the
transform by a unit complex phase, preserving its norm. Real weights also make
the norm even in frequency. These identities apply before any normalization.
-/

open scoped BigOperators

namespace LpSelfSimilar.Fourier

/-- Scaling all atom locations scales the angular frequency. -/
theorem finiteTransform_scale {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (b s : ℝ) :
    finiteTransform p (fun i ↦ b * z i) s = finiteTransform p z (s * b) := by
  unfold finiteTransform
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc]

/-- Translating all atom locations multiplies the transform by the corresponding phase. -/
theorem finiteTransform_translate {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (b s : ℝ) :
    finiteTransform p (fun i ↦ z i + b) s =
      finiteTransform p z s * Complex.exp ((s * b : ℝ) * Complex.I) := by
  simp only [finiteTransform, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- Translating a finite real law leaves the Fourier norm unchanged. -/
theorem norm_finiteTransform_translate {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (b s : ℝ) :
    ‖finiteTransform p (fun i ↦ z i + b) s‖ = ‖finiteTransform p z s‖ := by
  rw [finiteTransform_translate, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- The Fourier norm of a finite real law is even in frequency. -/
theorem norm_finiteTransform_neg {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (s : ℝ) :
    ‖finiteTransform p z (-s)‖ = ‖finiteTransform p z s‖ := by
  have he : ‖finiteTransform p z (-s)‖ ^ 2 = ‖finiteTransform p z s‖ ^ 2 := by
    rw [sq_norm_finiteTransform, sq_norm_finiteTransform]
    simp only [neg_mul, Real.cos_neg]
  nlinarith [norm_nonneg (finiteTransform p z (-s)), norm_nonneg (finiteTransform p z s)]

/-- Absolute frequency has the same Fourier norm. -/
theorem norm_finiteTransform_abs {ι : Type*} [Fintype ι]
    (p z : ι → ℝ) (s : ℝ) :
    ‖finiteTransform p z |s|‖ = ‖finiteTransform p z s‖ := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]
  · rw [abs_of_nonpos hs, norm_finiteTransform_neg]

end LpSelfSimilar.Fourier
