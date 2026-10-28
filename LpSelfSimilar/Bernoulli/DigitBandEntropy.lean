module

public import LpSelfSimilar.Entropy.FiniteLawBandEntropy
public import LpSelfSimilar.Bernoulli.FiniteBounds

@[expose] public section

/-!
# Integrated band entropy for actual Bernoulli digit laws

The PMF is the pushforward of independent fair words already connected to the
canonical Bernoulli series. Entropy and separation concern its actual atoms,
so collisions between words are allowed. The finite-law argument derives the
support bound and supplies the exact integral estimate without analytic inputs.
-/

open MeasureTheory Set LpSelfSimilar.Entropy
open scoped BigOperators

namespace LpSelfSimilar.Bernoulli

/-- The integrated entropy budget for the first `n` independent fair signed digits. -/
theorem digit_band_entropy_integral_lower_bound
    (θ ρ c L : ℝ) (n : ℕ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hρ : ρ ∈ Icc 0 1) (hc : c ∈ Icc 0 1) (hL : 1 ≤ L)
    (hentropy : ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ x ∈ (digitPMF θ n).support, ∀ y ∈ (digitPMF θ n).support, x ≠ y →
      (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    4 * (1 - c) * ρ * n - 4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) ≤
      ∫ j in c * ρ * n..L * n + 4,
        finiteLawBandEntropyBits (digitPMF θ n) (digitPMF_support_finite θ n)
          ((2 : ℝ) ^ (-j)) := by
  apply finiteLawBandEntropy_integral_lower_bound (digitPMF θ n)
    (digitPMF_support_finite θ n) θ ρ c L n hθ1 hρ hc hL ?_ hentropy hsep
  intro x hx
  simpa only [one_div] using abs_le.mpr (digitPMF_support_subset_interval hθ0 hθ1 n hx)

/-- The exact specialization `c = 4/25`, together with the stated large-scale constant bound. -/
theorem digit_band_entropy_integral_lower_bound_explicit
    (θ ρ L : ℝ) (n : ℕ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hρ : ρ ∈ Icc 0 1) (hL : 1 ≤ L)
    (hentropy : ρ * n ≤ finiteEntropy (digitPMF θ n) (digitPMF_support_finite θ n) / Real.log 2)
    (hsep : ∀ x ∈ (digitPMF θ n).support, ∀ y ∈ (digitPMF θ n).support, x ≠ y →
      (2 : ℝ) ^ (-(L * n)) ≤ |x - y|)
    (hconstant : Real.log (2 / (1 - θ) + 2) / Real.log 2 ≤ L + 2) :
    (84 / 25 : ℝ) * ρ * n - 4 * (L + 2) ≤
      ∫ j in (4 / 25 : ℝ) * ρ * n..L * n + 4,
        finiteLawBandEntropyBits (digitPMF θ n) (digitPMF_support_finite θ n)
          ((2 : ℝ) ^ (-j)) := by
  have h := digit_band_entropy_integral_lower_bound θ ρ (4 / 25) L n hθ0 hθ1
    hρ (by norm_num) hL hentropy hsep
  norm_num at h
  linarith

end LpSelfSimilar.Bernoulli
