import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem P2' {a b c : ℝ} : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 4 + b ^ 4 + c ^ 4 := by
  have hnum : (0 : ℝ) ≤ a^4 - a^2*b*c - a*b^2*c - a*b*c^2 + b^4 + c^4 := by
    have hbackend : (0 : ℝ) ≤ ((a)^4) + ((-1)*((a)^2)*(b)*(c)) + ((-1)*(a)*((b)^2)*(c)) + ((-1)*(a)*(b)*((c)^2)) + ((b)^4) + ((c)^4) := by
      have hs0 : (0 : ℝ) ≤ (1/1)*(-(1/3)*(a^2) - (1/3)*a*b - (1/3)*(b^2) + c^2)^2 + (3/2)*(-(1/3)*(a^2) - (1/6)*a*b - (1/6)*a*c + (2/3)*b*c)^2 + (9/8)*(-(4/9)*(a^2) - (1/9)*a*b - (1/3)*a*c + (8/9)*(b^2))^2 + (2/1)*(-(1/4)*(a^2) - (1/4)*a*b + (1/2)*a*c)^2 + (8/3)*(-(3/8)*(a^2) + (3/8)*a*b)^2 + (0/1)*(0)^2 := by positivity
      have hid : (((a)^4) + ((-1)*((a)^2)*(b)*(c)) + ((-1)*(a)*((b)^2)*(c)) + ((-1)*(a)*(b)*((c)^2)) + ((b)^4) + ((c)^4)) = (((1/1)*(-(1/3)*(a^2) - (1/3)*a*b - (1/3)*(b^2) + c^2)^2 + (3/2)*(-(1/3)*(a^2) - (1/6)*a*b - (1/6)*a*c + (2/3)*b*c)^2 + (9/8)*(-(4/9)*(a^2) - (1/9)*a*b - (1/3)*a*c + (8/9)*(b^2))^2 + (2/1)*(-(1/4)*(a^2) - (1/4)*a*b + (1/2)*a*c)^2 + (8/3)*(-(3/8)*(a^2) + (3/8)*a*b)^2 + (0/1)*(0)^2)) := by ring
      rw [hid]
      linarith
    convert hbackend using 1 <;> ring
  rw [← sub_nonneg]
  convert hnum using 1 <;> ring



theorem P2 {a b c : ℝ} : a ^ 2 * b * c + b ^ 2 * c * a + c ^ 2 * a * b ≤ a ^ 4 + b ^ 4 + c ^ 4 := by
  exact @P2' a b c
