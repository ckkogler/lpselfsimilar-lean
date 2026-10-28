module

public import LpSelfSimilar.Algebraic.DigitSeparation
public import LpSelfSimilar.Algebraic.UnitDigits
public import LpSelfSimilar.Entropy.Grid

@[expose] public section

/-!
Algebraic separation resolves the actual Bernoulli digit law on fine grids.

This statement applies to all algebraic parameters, including units with word
collisions: only distinct atom values need to be separated. The resulting scale
entropy is the entropy of the true digit law. In the non-unit case, the proved
word injectivity identifies that entropy exactly with length*log(2).
-/

open LpSelfSimilar.Bernoulli LpSelfSimilar.Entropy

namespace LpSelfSimilar.Algebraic

theorem digitPMF_support_separation {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) (l : ℕ)
    {a b : ℝ} (ha : a ∈ (digitPMF x l).support) (hb : b ∈ (digitPMF x l).support)
    (hab : a ≠ b) : Real.exp (-complexity x * l) ≤ |a - b| := by
  simp only [digitPMF, PMF.support_map] at ha hb
  obtain ⟨u, _, rfl⟩ := ha
  obtain ⟨v, _, rfl⟩ := hb
  exact digitSum_separation hx hx0 hx1 hab

/-- At scales resolving all distinct atoms, random grid entropy is exactly the
Shannon entropy of the actual law, even when the word map has collisions. -/
theorem digit_gridEntropy_eq_entropy {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) (l : ℕ) {s : ℝ} (hs : 0 < s)
    (hsep : s ≤ Real.exp (-complexity x * l)) :
    gridEntropy (digitPMF x l) (digitPMF_support_finite _ _) s =
      finiteEntropy (digitPMF x l) (digitPMF_support_finite _ _) := by
  apply gridEntropy_eq_of_separated _ _ hs
  intro a ha b hb hab
  exact hsep.trans (digitPMF_support_separation hx hx0 hx1 l ha hb hab)

theorem digit_gridEntropy_of_not_isAlgebraicUnit {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hx0 : 0 < x) (hx1 : x < 1) (hu : ¬ IsAlgebraicUnit x) (l : ℕ)
    {s : ℝ} (hs : 0 < s) (hsep : s ≤ Real.exp (-complexity x * l)) :
    gridEntropy (digitPMF x l) (digitPMF_support_finite _ _) s = (l : ℝ) * Real.log 2 := by
  rw [digit_gridEntropy_eq_entropy hx hx0 hx1 l hs hsep,
    digit_entropy_of_not_isAlgebraicUnit hx0.ne' hu l]

end LpSelfSimilar.Algebraic
