import Mathlib

theorem real_p31 (a b c : ℝ) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) : √(a - 1) + √(b - 1) + √(c - 1) ≤ √(c * (a * b + 1)) := by
  have h1 : 0 ≤ a - 1 := by linarith
  have h2 : 0 ≤ b - 1 := by linarith
  have h3 : 0 ≤ c - 1 := by linarith
  have hab_nonneg : 0 ≤ a * b := by nlinarith [ha, hb]
  have hxy : √(a - 1) + √(b - 1) ≤ √(a * b) := by
    apply le_of_sq_le_sq
    · rw [Real.sq_sqrt hab_nonneg]
      nlinarith [Real.sq_sqrt h1, Real.sq_sqrt h2, sq_nonneg (√(a - 1) * √(b - 1) - 1)]
    · positivity
  have hbc_nonneg : 0 ≤ a * b + 1 := by nlinarith [hab_nonneg]
  have hxyc : √(a * b) + √(c - 1) ≤ √(c * (a * b + 1)) := by
    apply le_of_sq_le_sq
    · have hmul : 0 ≤ c * (a * b + 1) := by nlinarith [hc, hbc_nonneg]
      rw [Real.sq_sqrt hmul]
      nlinarith [Real.sq_sqrt hab_nonneg, Real.sq_sqrt h3,
        sq_nonneg (√(a * b) * √(c - 1) - 1)]
    · positivity
  nlinarith
