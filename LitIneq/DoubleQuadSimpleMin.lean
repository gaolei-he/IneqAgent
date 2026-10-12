import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

def quad (a b c d ee f x y : ℝ) : ℝ :=
  a * (x * x) + b * (y * y) + c * x * y + d * x + ee * y + f

theorem double_quad_simple_min :
    ∀ a b c d ee f x y : ℝ,
      0 < a → 0 < b → c = 0 →
        quad a b c d ee f x y ≥
          quad a b c d ee f (-d / (2 * a)) (-ee / (2 * b)) := by
  intro a b c d ee f x y ha hb hc
  subst c
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hb_ne : b ≠ 0 := ne_of_gt hb
  -- The difference between an arbitrary point and the minimizing point is a
  -- sum of two perfect squares (the x- and y-parts separate since c = 0).
  have hdiff :
      quad a b 0 d ee f x y - quad a b 0 d ee f (-d / (2 * a)) (-ee / (2 * b))
        = a * (x + d / (2 * a)) ^ 2 + b * (y + ee / (2 * b)) ^ 2 := by
    unfold quad
    field_simp [ha_ne, hb_ne]
    ring
  have hx_nonneg : 0 ≤ a * (x + d / (2 * a)) ^ 2 := by
    exact mul_nonneg (le_of_lt ha) (sq_nonneg _)
  have hy_nonneg : 0 ≤ b * (y + ee / (2 * b)) ^ 2 := by
    exact mul_nonneg (le_of_lt hb) (sq_nonneg _)
  have hdiff_nonneg : 0 ≤ quad a b 0 d ee f x y - quad a b 0 d ee f (-d / (2 * a)) (-ee / (2 * b)) := by
    rw [hdiff]
    exact add_nonneg hx_nonneg hy_nonneg
  linarith
