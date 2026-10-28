module

public import LpSelfSimilar.Fourier.BandShiftSpacing

@[expose] public section

/-!
# First-shift indices on a finite translated grid

An arithmetic grid with spacing `P*kappa` gives first-shift indices with exact
integer slope `-P`. Ordered distinct grid indices therefore leave a gap of at
least `P`, the condition needed to insert the finite phase padding.
-/

namespace LpSelfSimilar.Fourier

/-- The first-shift index is exactly affine in the natural grid index. -/
theorem bandFirstShift_on_grid {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (P : ℕ) (t R : ℝ) (i : ℕ) :
    bandFirstShift θ ((2 : ℝ) ^ (-((P : ℝ) * (-Real.log θ / Real.log 2) * ((i : ℝ) + t))))
        ((2 : ℝ) ^ (-R)) =
      bandFirstShift θ ((2 : ℝ) ^ (-((P : ℝ) * (-Real.log θ / Real.log 2) * t)))
        ((2 : ℝ) ^ (-R)) - (P : ℤ) * i := by
  have he : (P : ℝ) * (-Real.log θ / Real.log 2) * ((i : ℝ) + t) =
      (P : ℝ) * (-Real.log θ / Real.log 2) * t +
        (((P : ℤ) * i : ℤ) : ℝ) * (-Real.log θ / Real.log 2) := by
    push_cast
    ring
  rw [he, bandFirstShift_dyadic_add_grid_step hθ0 hθ1]

/-- Distinct ordered grid indices give first shifts separated by at least one full grid spacing. -/
theorem bandFirstShift_grid_gap {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (P : ℕ) (t R : ℝ) {i j : ℕ} (hij : i < j) :
    bandFirstShift θ ((2 : ℝ) ^ (-((P : ℝ) * (-Real.log θ / Real.log 2) * ((j : ℝ) + t))))
        ((2 : ℝ) ^ (-R)) + P ≤
      bandFirstShift θ ((2 : ℝ) ^ (-((P : ℝ) * (-Real.log θ / Real.log 2) * ((i : ℝ) + t))))
        ((2 : ℝ) ^ (-R)) := by
  have hp : P * i + P ≤ P * j := by
    simpa only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] using Nat.mul_le_mul_left P (Nat.succ_le_of_lt hij)
  have hp' : (P : ℤ) * i + P ≤ (P : ℤ) * j := by exact_mod_cast hp
  rw [bandFirstShift_on_grid hθ0 hθ1, bandFirstShift_on_grid hθ0 hθ1]
  omega

end LpSelfSimilar.Fourier
