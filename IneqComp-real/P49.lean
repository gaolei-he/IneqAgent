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

namespace Lean92.IneqComp_real_P49

theorem real_p49 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : 1 + 6 / (a * b + a * c + a * d + b * c + b * d + c * d) ≥ 8 / (a + b + c + d) := by
  have hnum : (0 : ℝ) ≤ a^2*b + a^2*c + a^2*d + a*b^2 + 3*a*b*c + 3*a*b*d - 8*a*b + a*c^2 + 3*a*c*d - 8*a*c + a*d^2 - 8*a*d + 6*a + b^2*c + b^2*d + b*c^2 + 3*b*c*d - 8*b*c + b*d^2 - 8*b*d + 6*b + c^2*d + c*d^2 - 8*c*d + 6*c + 6*d := by
    have hbackend : (0 : ℝ) ≤ (((a)^2)*(b)) + (((a)^2)*(c)) + (((a)^2)*(d)) + ((a)*((b)^2)) + ((3)*(a)*(b)*(c)) + ((3)*(a)*(b)*(d)) + ((-1)*(8)*(a)*(b)) + ((a)*((c)^2)) + ((3)*(a)*(c)*(d)) + ((-1)*(8)*(a)*(c)) + ((a)*((d)^2)) + ((-1)*(8)*(a)*(d)) + ((6)*(a)) + (((b)^2)*(c)) + (((b)^2)*(d)) + ((b)*((c)^2)) + ((3)*(b)*(c)*(d)) + ((-1)*(8)*(b)*(c)) + ((b)*((d)^2)) + ((-1)*(8)*(b)*(d)) + ((6)*(b)) + (((c)^2)*(d)) + ((c)*((d)^2)) + ((-1)*(8)*(c)*(d)) + ((6)*(c)) + ((6)*(d)) := by
      have hgg1 : (0 : ℝ) ≤ a := by first | positivity | nlinarith
      have hsg1 : (0 : ℝ) ≤ (1/6)*((6/1) - (2/1)*b - (2/1)*c - (2/1)*d)^2 + (3/1)*(-(1/6)*b - (1/6)*c + (1/3)*d)^2 + (4/1)*(-(1/4)*b + (1/4)*c)^2 + (0/1)*(0/1)^2 := by positivity
      have hpg1 := mul_nonneg hsg1 hgg1
      have hgg2 : (0 : ℝ) ≤ b := by first | positivity | nlinarith
      have hsg2 : (0 : ℝ) ≤ (1/6)*((6/1) - (2/1)*a - (2/1)*c - (2/1)*d)^2 + (3/1)*(-(1/6)*a - (1/6)*c + (1/3)*d)^2 + (4/1)*(-(1/4)*a + (1/4)*c)^2 + (0/1)*(0/1)^2 := by positivity
      have hpg2 := mul_nonneg hsg2 hgg2
      have hgg3 : (0 : ℝ) ≤ c := by first | positivity | nlinarith
      have hsg3 : (0 : ℝ) ≤ (1/6)*((6/1) - (2/1)*a - (2/1)*b - (2/1)*d)^2 + (3/1)*(-(1/6)*a - (1/6)*b + (1/3)*d)^2 + (4/1)*(-(1/4)*a + (1/4)*b)^2 + (0/1)*(0/1)^2 := by positivity
      have hpg3 := mul_nonneg hsg3 hgg3
      have hgg4 : (0 : ℝ) ≤ d := by first | positivity | nlinarith
      have hsg4 : (0 : ℝ) ≤ (1/6)*((6/1) - (2/1)*a - (2/1)*b - (2/1)*c)^2 + (3/1)*(-(1/6)*a - (1/6)*b + (1/3)*c)^2 + (4/1)*(-(1/4)*a + (1/4)*b)^2 + (0/1)*(0/1)^2 := by positivity
      have hpg4 := mul_nonneg hsg4 hgg4
      have hs0 : (0 : ℝ) ≤ (0)*(1)^2 := by positivity
      have hid : ((((a)^2)*(b)) + (((a)^2)*(c)) + (((a)^2)*(d)) + ((a)*((b)^2)) + ((3)*(a)*(b)*(c)) + ((3)*(a)*(b)*(d)) + ((-1)*(8)*(a)*(b)) + ((a)*((c)^2)) + ((3)*(a)*(c)*(d)) + ((-1)*(8)*(a)*(c)) + ((a)*((d)^2)) + ((-1)*(8)*(a)*(d)) + ((6)*(a)) + (((b)^2)*(c)) + (((b)^2)*(d)) + ((b)*((c)^2)) + ((3)*(b)*(c)*(d)) + ((-1)*(8)*(b)*(c)) + ((b)*((d)^2)) + ((-1)*(8)*(b)*(d)) + ((6)*(b)) + (((c)^2)*(d)) + ((c)*((d)^2)) + ((-1)*(8)*(c)*(d)) + ((6)*(c)) + ((6)*(d))) = (((0)*(1)^2) + ((1/6)*((6/1) - (2/1)*b - (2/1)*c - (2/1)*d)^2 + (3/1)*(-(1/6)*b - (1/6)*c + (1/3)*d)^2 + (4/1)*(-(1/4)*b + (1/4)*c)^2 + (0/1)*(0/1)^2)*(a) + ((1/6)*((6/1) - (2/1)*a - (2/1)*c - (2/1)*d)^2 + (3/1)*(-(1/6)*a - (1/6)*c + (1/3)*d)^2 + (4/1)*(-(1/4)*a + (1/4)*c)^2 + (0/1)*(0/1)^2)*(b) + ((1/6)*((6/1) - (2/1)*a - (2/1)*b - (2/1)*d)^2 + (3/1)*(-(1/6)*a - (1/6)*b + (1/3)*d)^2 + (4/1)*(-(1/4)*a + (1/4)*b)^2 + (0/1)*(0/1)^2)*(c) + ((1/6)*((6/1) - (2/1)*a - (2/1)*b - (2/1)*c)^2 + (3/1)*(-(1/6)*a - (1/6)*b + (1/3)*c)^2 + (4/1)*(-(1/4)*a + (1/4)*b)^2 + (0/1)*(0/1)^2)*(d)) := by ring
      rw [hid]
      linarith
    convert hbackend using 1 <;> ring
  change _ ≤ _
  rw [← sub_nonneg]
  have hden1_pos : 0 < a + b + c + d := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd]
  have hden1_ne : a + b + c + d ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < a*b + a*c + a*d + b*c + b*d + c*d := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd]
  have hden2_ne : a*b + a*c + a*d + b*c + b*d + c*d ≠ 0 := ne_of_gt hden2_pos
  have hden : (0 : ℝ) < a^2*b + a^2*c + a^2*d + a*b^2 + 3*a*b*c + 3*a*b*d + a*c^2 + 3*a*c*d + a*d^2 + b^2*c + b^2*d + b*c^2 + 3*b*c*d + b*d^2 + c^2*d + c*d^2 := by positivity
  have hfrac : (1 + 6/(a*b + a*c + a*d + b*c + b*d + c*d) - 8/(a + b + c + d)) = (a^2*b + a^2*c + a^2*d + a*b^2 + 3*a*b*c + 3*a*b*d - 8*a*b + a*c^2 + 3*a*c*d - 8*a*c + a*d^2 - 8*a*d + 6*a + b^2*c + b^2*d + b*c^2 + 3*b*c*d - 8*b*c + b*d^2 - 8*b*d + 6*b + c^2*d + c*d^2 - 8*c*d + 6*c + 6*d) / (a^2*b + a^2*c + a^2*d + a*b^2 + 3*a*b*c + 3*a*b*d + a*c^2 + 3*a*c*d + a*d^2 + b^2*c + b^2*d + b*c^2 + 3*b*c*d + b*d^2 + c^2*d + c*d^2) := by
    field_simp
    <;> ring
  have hgoal : (0 : ℝ) ≤ 1 + 6/(a*b + a*c + a*d + b*c + b*d + c*d) - 8/(a + b + c + d) := by
    rw [hfrac]
    exact div_nonneg hnum (le_of_lt hden)
  convert hgoal using 1 <;> field_simp <;> ring

end Lean92.IneqComp_real_P49


theorem real_p49 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : 1 + 6 / (a * b + a * c + a * d + b * c + b * d + c * d) ≥ 8 / (a + b + c + d) := by
  exact @Lean92.IneqComp_real_P49.real_p49 a b c d ha hb hc hd

#print axioms real_p49
