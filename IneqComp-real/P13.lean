import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.GCongr
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace Lean92.IneqComp_real_P13

theorem real_p13 (a b c : ℝ) : (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ 3 * (a + b + c)^2 := by
  have hnum : (0 : ℝ) ≤ a^2*b^2*c^2 + 2*a^2*b^2 + 2*a^2*c^2 + a^2 - 6*a*b - 6*a*c + 2*b^2*c^2 + b^2 - 6*b*c + c^2 + 8 := by
    have hbackend : (0 : ℝ) ≤ (((a)^2)*((b)^2)*((c)^2)) + ((2)*((a)^2)*((b)^2)) + ((2)*((a)^2)*((c)^2)) + ((a)^2) + ((-1)*(6)*(a)*(b)) + ((-1)*(6)*(a)*(c)) + ((2)*((b)^2)*((c)^2)) + ((b)^2) + ((-1)*(6)*(b)*(c)) + ((c)^2) + (8) := by
      have hs0 : (0 : ℝ) ≤ (1/8)*((8/1) - (8/3)*a*b - (8/3)*a*c - (8/3)*b*c)^2 + (1/1)*(-(1/3)*a - (1/3)*b + c - (1/3)*a*b*c)^2 + (9/8)*(-(4/9)*a + (8/9)*b - (4/9)*a*b*c)^2 + (3/2)*((2/3)*a - (2/3)*a*b*c)^2 + (9/10)*(-(5/9)*a*b - (5/9)*a*c + (10/9)*b*c)^2 + (6/5)*(-(5/6)*a*b + (5/6)*a*c)^2 + (0/1)*(0/1)^2 + (0/1)*(0/1)^2 := by positivity
      have hid : ((((a)^2)*((b)^2)*((c)^2)) + ((2)*((a)^2)*((b)^2)) + ((2)*((a)^2)*((c)^2)) + ((a)^2) + ((-1)*(6)*(a)*(b)) + ((-1)*(6)*(a)*(c)) + ((2)*((b)^2)*((c)^2)) + ((b)^2) + ((-1)*(6)*(b)*(c)) + ((c)^2) + (8)) = (((1/8)*((8/1) - (8/3)*a*b - (8/3)*a*c - (8/3)*b*c)^2 + (1/1)*(-(1/3)*a - (1/3)*b + c - (1/3)*a*b*c)^2 + (9/8)*(-(4/9)*a + (8/9)*b - (4/9)*a*b*c)^2 + (3/2)*((2/3)*a - (2/3)*a*b*c)^2 + (9/10)*(-(5/9)*a*b - (5/9)*a*c + (10/9)*b*c)^2 + (6/5)*(-(5/6)*a*b + (5/6)*a*c)^2 + (0/1)*(0/1)^2 + (0/1)*(0/1)^2)) := by ring
      rw [hid]
      linarith
    convert hbackend using 1 <;> ring
  change _ ≤ _
  rw [← sub_nonneg]
  convert hnum using 1 <;> ring

end Lean92.IneqComp_real_P13


theorem real_p13 (a b c : ℝ) : (a^2 + 2) * (b^2 + 2) * (c^2 + 2) ≥ 3 * (a + b + c)^2 := by
  exact @Lean92.IneqComp_real_P13.real_p13 a b c

#print axioms real_p13
