module

public import LpSelfSimilar.Fourier.ScaledBandShift

@[expose] public section

/-!
# Exact spacing and padding for shifted digit blocks

An integer multiple of the dyadic logarithmic spacing translates the first
shift by precisely the opposite integer. Consequently equally spaced scale
samples leave disjoint digit intervals even after the bounded extra shifts
used for phase cancellation. No random labels enter these index choices.
-/

namespace LpSelfSimilar.Fourier

/-- A logarithmic grid step produces the exact opposite change of first shift. -/
theorem bandFirstShift_dyadic_add_grid_step {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (j R : ℝ) (m : ℤ) :
    bandFirstShift θ ((2 : ℝ) ^ (-(j + (m : ℝ) * ((-Real.log θ) / Real.log 2))))
        ((2 : ℝ) ^ (-R)) =
      bandFirstShift θ ((2 : ℝ) ^ (-j)) ((2 : ℝ) ^ (-R)) - m := by
  have hlog : Real.log θ ≠ 0 := (Real.log_neg hθ0 hθ1).ne
  have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [bandFirstShift_dyadic hθ0 hθ1, bandFirstShift_dyadic hθ0 hθ1]
  have he : (R - (j + (m : ℝ) * ((-Real.log θ) / Real.log 2)) -
      Real.log (Real.pi / θ) / Real.log 2) / ((-Real.log θ) / Real.log 2) =
      (R - j - Real.log (Real.pi / θ) / Real.log 2) /
        ((-Real.log θ) / Real.log 2) - (m : ℝ) := by
    field_simp [hlog, hlog2]
    <;> ring
  rw [he, Int.ceil_sub_intCast]

/-- Padding by `n+K+2` separates the actual digit positions after any extra shifts in `[0,K]`. -/
theorem padded_shift_digit_positions_lt (a b : ℤ) (n K k l i j : ℕ)
    (hgap : b + (n : ℤ) + K + 2 ≤ a) (hl : l ≤ K) (hj : j < n) :
    b + (l : ℤ) + j < a + (k : ℤ) + i := by
  omega

end LpSelfSimilar.Fourier
