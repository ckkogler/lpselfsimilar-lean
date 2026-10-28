module

public import LpSelfSimilar.Entropy.DistanceBandEntropyBudget

@[expose] public section

/-!
# Distance-band entropy of finitely supported real probability laws

Vertices are the actual atoms of the law, so repeated descriptions of an atom
are merged before computing entropy. The supplied finite-support proof bounds
an actual PMF support; it is not a substitute for a probability or entropy input.
-/

open MeasureTheory
open scoped BigOperators

namespace LpSelfSimilar.Entropy

/-- Maximum conditional entropy in bits on the actual atoms of a finite real law. -/
noncomputable def finiteLawBandEntropyBits (p : PMF ℝ) (hp : p.support.Finite) (a : ℝ) : ℝ :=
  distanceBandConditionalEntropyBits (fun x : hp.toFinset ↦ (x : ℝ)) a
    (fun x ↦ (p x).toReal)

/-- The finite-law integrated band budget, on actual merged atoms. -/
theorem finiteLawBandEntropy_integral_lower_bound
    (p : PMF ℝ) (hp : p.support.Finite) (θ ρ c L : ℝ) (n : ℕ)
    (hθ : θ < 1) (hρ : ρ ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) (hL : 1 ≤ L)
    (hz : ∀ x ∈ p.support, |x| ≤ 1 / (1 - θ))
    (hentropy : ρ * n ≤ finiteEntropy p hp / Real.log 2)
    (hsep : ∀ x ∈ p.support, ∀ y ∈ p.support, x ≠ y →
      (2 : ℝ) ^ (-(L * n)) ≤ |x - y|) :
    4 * (1 - c) * ρ * n - 4 * (Real.log (2 / (1 - θ) + 2) / Real.log 2) ≤
      ∫ j in c * ρ * n..L * n + 4, finiteLawBandEntropyBits p hp ((2 : ℝ) ^ (-j)) := by
  have hprob : ∑ x : hp.toFinset, (p x).toReal = 1 := by
    change (∑ x ∈ hp.toFinset.attach, (p x.val).toReal) = 1
    rw [Finset.sum_attach hp.toFinset (fun x : ℝ ↦ (p x).toReal)]
    exact sum_support_toReal p hp
  have hentropy' : ρ * n ≤
      (∑ x : hp.toFinset, Real.negMulLog (p x).toReal) / Real.log 2 := by
    change ρ * n ≤ (∑ x ∈ hp.toFinset.attach, Real.negMulLog (p x.val).toReal) / Real.log 2
    rw [Finset.sum_attach hp.toFinset (fun x : ℝ ↦ Real.negMulLog (p x).toReal)]
    exact hentropy
  apply distanceBand_integrated_entropy_budget
    (fun x : hp.toFinset ↦ (x : ℝ)) (fun x ↦ (p x).toReal)
    (fun _ ↦ ENNReal.toReal_nonneg) hprob θ ρ c L n hθ hρ hc hL
    (fun x ↦ hz x (hp.mem_toFinset.mp x.property)) hentropy'
  intro x y hxy
  exact hsep x (hp.mem_toFinset.mp x.property) y (hp.mem_toFinset.mp y.property)
    (fun he ↦ hxy (Subtype.ext he))

end LpSelfSimilar.Entropy
