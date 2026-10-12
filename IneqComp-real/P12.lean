import Mathlib

theorem real_p12 (a b : ℝ) (hab : a * b > 0) : (a^4 + 4 * b^4 + 1) / (a * b) ≥ 4 := by
  have hsquare1 : 0 ≤ (a^2 - 2 * b^2)^2 := sq_nonneg (a^2 - 2 * b^2)
  have hfourth : a^4 + 4 * b^4 ≥ 4 * (a * b)^2 := by
    nlinarith [hsquare1]
  have hsquare2 : 0 ≤ (2 * (a * b) - 1)^2 := sq_nonneg (2 * (a * b) - 1)
  have hcross : 4 * (a * b)^2 + 1 ≥ 4 * (a * b) := by
    nlinarith [hsquare2]
  have hmain : a^4 + 4 * b^4 + 1 ≥ 4 * (a * b) := by
    nlinarith [hfourth, hcross]
  exact (le_div_iff₀ hab).mpr hmain
