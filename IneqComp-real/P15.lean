import Mathlib

theorem real_p15 (a b : ℝ) (h : a - 3 * b + 6 = 0) : (2 : ℝ) ^ a + 1 / ((8 : ℝ) ^ b) ≥ 1 / 4 := by
  have ha : a = 3 * b - 6 := by linarith
  have hpow : (2 : ℝ) ^ a = (8 : ℝ) ^ b / 64 := by
    rw [ha]
    calc
      (2 : ℝ) ^ (3 * b - 6) = (2 : ℝ) ^ (3 * b) / (2 : ℝ) ^ (6 : ℝ) := by
        rw [Real.rpow_sub]
        norm_num
      _ = (8 : ℝ) ^ b / 64 := by
        rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
  have hx : 0 < (8 : ℝ) ^ b := by positivity
  have hsq : 0 ≤ ((8 : ℝ) ^ b - 8) ^ 2 := sq_nonneg ((8 : ℝ) ^ b - 8)
  have hx0 : (8 : ℝ) ^ b ≠ 0 := ne_of_gt hx
  have hineq : (8 : ℝ) ^ b / 64 + 1 / (8 : ℝ) ^ b ≥ 1 / 4 := by
    change 1 / 4 ≤ (8 : ℝ) ^ b / 64 + 1 / (8 : ℝ) ^ b
    rw [← sub_nonneg]
    field_simp [hx0]
    nlinarith [hsq]
  rw [hpow]
  exact hineq
