import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

theorem quadratic :
    ∀ a b c t : ℝ,
      a > 0 →
      a * (t * t) + b * t + c < 0 →
      b * b > 4 * a * c := by
  intro a b c t ha hlt
  by_contra h
  push Not at h
  -- The square term is always nonnegative.
  have hsq : (0 : ℝ) ≤ (2 * a * t + b) ^ 2 := sq_nonneg (2 * a * t + b)
  -- If b * b ≤ 4 * a * c, the complement 4 * a * c - b * b is nonnegative.
  have hdisc : (0 : ℝ) ≤ 4 * a * c - b * b := by linarith
  have hsqsum : (0 : ℝ) ≤ (2 * a * t + b) ^ 2 + (4 * a * c - b * b) :=
    add_nonneg hsq hdisc
  -- Scaling the quadratic by the positive quantity 4 * a gives an identity:
  --   4 * a * (a*t^2 + b*t + c) = (2*a*t + b)^2 + (4*a*c - b^2).
  have hid :
      4 * a * (a * (t * t) + b * t + c) =
        (2 * a * t + b) ^ 2 + (4 * a * c - b * b) := by
    ring
  -- Since a > 0 and the quadratic value is negative, the scaled value is negative.
  have hscaled_neg : 4 * a * (a * (t * t) + b * t + c) < 0 := by
    exact mul_neg_of_pos_of_neg (by positivity) hlt
  rw [hid] at hscaled_neg
  linarith
