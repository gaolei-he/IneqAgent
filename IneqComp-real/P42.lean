import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem real_p42' (x y z : ℝ) (h : x * y + y * z + z * x = -1) : x^2 + 5 * y^2 + 8 * z^2 ≥ 4 := by
  have hnum : (0 : ℝ) ≤ x^2 + 5*y^2 + 8*z^2 - 4 := by
    have hbackend : (0 : ℝ) ≤ ((x)^2) + ((5)*((y)^2)) + ((8)*((z)^2)) + (-4) := by
      have heh1 : (((x)*(y)) + ((x)*(z)) + ((y)*(z)) + (1)) = (0 : ℝ) := by nlinarith
      have hzh1 : (-4/1) * (((x)*(y)) + ((x)*(z)) + ((y)*(z)) + (1)) = (0 : ℝ) := by rw [heh1]; ring
      have hs0 : (0 : ℝ) ≤ (1/8)*((2/1)*x + (2/1)*y + (8/1)*z)^2 + (2/9)*((3/2)*x + (9/2)*y)^2 + (0/1)*(0)^2 := by positivity
      have hid : (((x)^2) + ((5)*((y)^2)) + ((8)*((z)^2)) + (-4)) = (((1/8)*((2/1)*x + (2/1)*y + (8/1)*z)^2 + (2/9)*((3/2)*x + (9/2)*y)^2 + (0/1)*(0)^2) + (-4/1)*(((x)*(y)) + ((x)*(z)) + ((y)*(z)) + (1))) := by ring
      rw [hid]
      linarith
    convert hbackend using 1 <;> ring
  change _ ≤ _
  rw [← sub_nonneg]
  convert hnum using 1 <;> ring



theorem real_p42 (x y z : ℝ) (h : x * y + y * z + z * x = -1) : x^2 + 5 * y^2 + 8 * z^2 ≥ 4 := by
  exact @real_p42' x y z h
