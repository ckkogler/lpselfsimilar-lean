module

public import LpSelfSimilar.Analysis.ConjugateDensity
public import LpSelfSimilar.Analysis.ConvolutionExponents
public import LpSelfSimilar.Probability.FiniteConvolution

@[expose] public section

/-!
Iteration of Young's inequality for a finite family. After n<k factors with
L^(k/(k-1)) densities the convolution has exponent k/(k-n); the last factor
then yields a continuous density by the conjugate-exponent theorem.
-/

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace LpSelfSimilar

lemma isFiniteMeasure_of_integrable_density {μ : Measure ℝ} {f : ℝ → ℝ}
    (hf : Integrable f volume) (hn : ∀ x, 0 ≤ f x)
    (hμ : μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x))) : IsFiniteMeasure μ := by
  rw [hμ]
  apply isFiniteMeasure_withDensity
  have h := hf.hasFiniteIntegral
  exact (show (∫⁻ x, ENNReal.ofReal (f x)) < ∞ by
    simpa only [HasFiniteIntegral, Real.enorm_eq_ofReal (hn _)] using h).ne

/-- Iterated Young inequality, with no assumed density of any partial convolution. -/
theorem exists_density_finiteConvolution_memLp {k n : ℕ} (hn : 1 ≤ n) (hnk : n < k)
    (μ : Fin n → Measure ℝ)
    (hμ : ∀ i, ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      μ i = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      MemLp f (ENNReal.ofReal (convolutionExponent k 1)) volume) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      finiteConvolution μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      MemLp f (ENNReal.ofReal (convolutionExponent k n)) volume := by
  induction n with
  | zero => omega
  | succ n ih =>
    obtain ⟨f, hfn, hf, hfμ, hfp⟩ := hμ 0
    by_cases hn0 : n = 0
    · subst n
      haveI := isFiniteMeasure_of_integrable_density hf hfn hfμ
      refine ⟨f, hfn, hf, ?_, hfp⟩
      simpa only [finiteConvolution, conv_dirac_zero] using hfμ
    · obtain ⟨g, hgn, hg, hgμ, hgp⟩ := ih (by omega) (by omega)
        (fun i ↦ μ i.succ) (fun i ↦ hμ i.succ)
      have hn1 : 1 ≤ n := by omega
      have hp := convolutionExponent_pos (show 1 < k by omega)
      have hq := convolutionExponent_pos (show n < k by omega)
      have hr := convolutionExponent_pos hnk
      have hsum := convolutionExponent_young hn1 hnk
      have h := exists_density_convolution_memLp hf hg hfn hgn hfμ hgμ hp hq hr
        (convolutionExponent_mono (by omega) hnk)
        (convolutionExponent_mono (by omega) hnk) (by linarith) hfp hgp
      exact h

/-- A k-fold convolution of L^(k/(k-1)) densities has a continuous density. -/
theorem exists_continuous_density_finiteConvolution {k : ℕ} (hk : 2 ≤ k)
    (μ : Fin k → Measure ℝ)
    (hμ : ∀ i, ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Integrable f volume ∧
      μ i = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) ∧
      MemLp f (ENNReal.ofReal (convolutionExponent k 1)) volume) :
    ∃ f : ℝ → ℝ, (∀ x, 0 ≤ f x) ∧ Continuous f ∧ Integrable f volume ∧
      finiteConvolution μ = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨f, hfn, hf, hfμ, hfp⟩ := hμ 0
  obtain ⟨g, hgn, hg, hgμ, hgp⟩ := exists_density_finiteConvolution_memLp
    (k := n + 1) (by omega : 1 ≤ n) (by omega)
    (fun i : Fin n ↦ μ i.succ) (fun i ↦ hμ i.succ)
  have he : convolutionExponent (n + 1) n = (n + 1 : ℕ) := by
    simpa using convolutionExponent_pred (show 1 ≤ n + 1 by omega)
  rw [he] at hgp
  have hs := convolutionExponent_conjugate hk
  exact exists_continuous_density_convolution hf hg hfn hgn hfμ hgμ
    (one_le_convolutionExponent (by omega)) (by exact_mod_cast (show 1 ≤ n + 1 by omega))
    (by linarith) hfp hgp

end LpSelfSimilar
