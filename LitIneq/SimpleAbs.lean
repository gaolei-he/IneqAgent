import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

theorem simple_abs :
    ∀ x y : ℝ, 0 < y → |x * y| ≤ 1 → x * y ≤ |x| * y := by
  intro x y hy _
  have hx_le_abs : x ≤ |x| := le_abs_self x
  have hy_nonneg : 0 ≤ y := le_of_lt hy
  exact mul_le_mul_of_nonneg_right hx_le_abs hy_nonneg
