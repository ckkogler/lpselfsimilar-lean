module

public import LpSelfSimilar.Bernoulli.ConvolutionPowers
public import LpSelfSimilar.Analysis.FiniteYoungConvolution
public import LpSelfSimilar.Analysis.ScaledDensity
public import LpSelfSimilar.Analysis.ContinuousDensitySupport

@[expose] public section

/-!
The final convolution argument: a density at exponent k/(k-1) for the kth
parameter power gives a continuous compactly supported density for the original
Bernoulli convolution. The residue-law identity supplies all scaled factors.
-/

open MeasureTheory Set

namespace LpSelfSimilar.Bernoulli

theorem continuous_density_of_power_memLp {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1)
    {k : ℕ} (hk : 2 ≤ k) {f : ℝ → ℝ} (hf : Integrable f volume)
    (hn : ∀ x, 0 ≤ f x)
    (hrep : convolution (l ^ k) = volume.withDensity (fun x ↦ ENNReal.ofReal (f x)))
    (hLp : MemLp f (ENNReal.ofReal ((k : ℝ) / ((k : ℝ) - 1))) volume) :
    ∃ g : ℝ → ℝ, (∀ x, 0 ≤ g x) ∧ Continuous g ∧ HasCompactSupport g ∧
      convolution l = volume.withDensity (fun x ↦ ENNReal.ofReal (g x)) := by
  have hfamily (j : Fin k) := exists_density_map_mul_pos (pow_pos hl0 (j : ℕ)) hf hn hrep hLp
  have hex := exists_continuous_density_finiteConvolution hk
    (fun j : Fin k ↦ (convolution (l ^ k)).map (fun x ↦ l ^ (j : ℕ) * x))
    (by intro j; simpa only [convolutionExponent, Nat.cast_one] using hfamily j)
  obtain ⟨g, hgn, hgc, hgi, hgrep⟩ := hex
  have he := convolution_eq_finiteConvolution_power (r := l) (by simpa [abs_of_pos hl0] using hl1)
    (show 0 < k by omega)
  rw [← he] at hgrep
  refine ⟨g, hgn, hgc, ?_, hgrep⟩
  exact hasCompactSupport_of_density hgi hgn hgc hgrep isCompact_Icc
    (convolution_compl_interval l hl0.le hl1)

end LpSelfSimilar.Bernoulli
