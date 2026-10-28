module

public import LpSelfSimilar.Analysis.FiniteCosineDerivative
public import Mathlib.Analysis.Complex.RealDeriv

@[expose] public section

/-!
# The sharp low-frequency derivative error for finite cosine products

The derivative splits into the Gaussian derivative times the product and the
logarithmic remainder derivative times the product. The product lies between
zero and its Gaussian. Combining both proved remainder estimates gives exactly
chi*(abs(u)^5+4*abs(u)^3)/6 times the variance-matched Gaussian.
-/

namespace LpSelfSimilar.Analysis

/-- The actual real product derivative has the exact low-frequency Gaussian error. -/
theorem abs_deriv_prod_cos_add_gaussian_le {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (u χ : ℝ)
    (ha : ∀ i ∈ s, |a i * u| ≤ 1)
    (hsq : (∑ i ∈ s, a i ^ 2) ≤ 1) (hfour : (∑ i ∈ s, a i ^ 4) ≤ χ) :
    |deriv (fun v => ∏ i ∈ s, Real.cos (a i * v)) u +
      u * (∑ i ∈ s, a i ^ 2) * Real.exp (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2)| ≤
      (χ / 6 * (|u| ^ 5 + 4 * |u| ^ 3)) * Real.exp (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2) := by
  let P := ∏ i ∈ s, Real.cos (a i * u)
  let V := ∑ i ∈ s, a i ^ 2
  let D := ∑ i ∈ s, a i * (Real.tan (a i * u) - a i * u)
  let G := Real.exp (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hχ : 0 ≤ χ :=
    (show 0 ≤ ∑ i ∈ s, a i ^ 4 from Finset.sum_nonneg (fun i hi => by positivity)).trans hfour
  have hG : 0 ≤ G := (Real.exp_pos _).le
  have hP : 0 ≤ P ∧ P ≤ G := prod_cos_nonneg_le_gaussian s a u ha
  have hE : |P - G| ≤ (χ * u ^ 4 / 6) * G := abs_prod_cos_sub_gaussian_le s a u χ ha hfour
  have hD : |D| ≤ ((2 / 3 : ℝ) * |u| ^ 3) * χ :=
    (abs_sum_tan_remainder_le s a u ha).trans
      (mul_le_mul_of_nonneg_left hfour (by positivity))
  have hT1 : (|u| * V) * |P-G| ≤ |u| * ((χ * u ^ 4 / 6) * G) := by
    calc
      _ ≤ (|u| * 1) * |P-G| := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (abs_nonneg u)) (abs_nonneg _)
      _ = |u| * |P-G| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (abs_nonneg u)
  have hT2 : |D| * P ≤ (((2 / 3 : ℝ) * |u| ^ 3) * χ) * G :=
    mul_le_mul hD hP.2 hP.1 (by positivity)
  rw [(hasDerivAt_prod_cos_quadratic_remainder s a u ha).deriv]
  change |(-(u * V) - D) * P + u * V * G| ≤ _
  have he : (-(u * V) - D) * P + u * V * G = (-u * V) * (P-G) + (-D) * P := by ring
  rw [he]
  calc
    _ ≤ |(-u * V) * (P-G)| + |(-D) * P| := abs_add_le _ _
    _ = (|u| * V) * |P-G| + |D| * P := by
      simp only [abs_mul, abs_neg, abs_of_nonneg hV, abs_of_nonneg hP.1]
    _ ≤ |u| * ((χ * u ^ 4 / 6) * G) + (((2 / 3 : ℝ) * |u| ^ 3) * χ) * G := add_le_add hT1 hT2
    _ = _ := by
      have hp : u ^ 4 = |u| ^ 4 := by
        rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ u ^ 4)]
      rw [hp]
      ring

/-- The same estimate holds for the actual complex-valued finite product derivative. -/
theorem norm_deriv_prod_cos_add_gaussian_le {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (u χ : ℝ)
    (ha : ∀ i ∈ s, |a i * u| ≤ 1)
    (hsq : (∑ i ∈ s, a i ^ 2) ≤ 1) (hfour : (∑ i ∈ s, a i ^ 4) ≤ χ) :
    ‖deriv (fun v => ∏ i ∈ s, (Real.cos (a i * v) : ℂ)) u +
      ((u * (∑ i ∈ s, a i ^ 2) * Real.exp (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2) : ℝ) : ℂ)‖ ≤
      (χ / 6 * (|u| ^ 5 + 4 * |u| ^ 3)) * Real.exp (-(u ^ 2) / 2 * ∑ i ∈ s, a i ^ 2) := by
  have h := abs_deriv_prod_cos_add_gaussian_le s a u χ ha hsq hfour
  have hd := hasDerivAt_prod_cos_quadratic_remainder s a u ha
  have he : (fun v => ∏ i ∈ s, (Real.cos (a i * v) : ℂ)) =
      (fun v => ((∏ i ∈ s, Real.cos (a i * v) : ℝ) : ℂ)) := by
    funext v
    simp only [Complex.ofReal_prod]
  rw [he, hd.ofReal_comp.deriv]
  rw [hd.deriv] at h
  simpa only [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs] using h

end LpSelfSimilar.Analysis
