import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem P1' {a b c : ℝ} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have hnum : (0 : ℝ) ≤ a^2 - a*b - a*c + b^2 - b*c + c^2 := by
    have hbackend : (0 : ℝ) ≤ ((a)^2) + ((-1)*(a)*(b)) + ((-1)*(a)*(c)) + ((b)^2) + ((-1)*(b)*(c)) + ((c)^2) := by
      have hs0 : (0 : ℝ) ≤ (1/1)*(-(1/2)*a - (1/2)*b + c)^2 + (4/3)*(-(3/4)*a + (3/4)*b)^2 + (0/1)*(0)^2 := by positivity
      have hid : (((a)^2) + ((-1)*(a)*(b)) + ((-1)*(a)*(c)) + ((b)^2) + ((-1)*(b)*(c)) + ((c)^2)) = (((1/1)*(-(1/2)*a - (1/2)*b + c)^2 + (4/3)*(-(3/4)*a + (3/4)*b)^2 + (0/1)*(0)^2)) := by ring
      rw [hid]
      linarith
    convert hbackend using 1 <;> ring
  rw [← sub_nonneg]
  convert hnum using 1 <;> ring



theorem P1 {a b c : ℝ} : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  exact @P1' a b c
