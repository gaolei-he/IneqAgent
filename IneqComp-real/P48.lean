import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem real_p48' (a b : ℝ) (ha : a > 0) (hb : b > 0) : (a + 1)^2 / b + (b + 3)^2 / a ≥ 16 := by
  have hnum : (0 : ℝ) ≤ a^3 + 2*a^2 - 16*a*b + a + b^3 + 6*b^2 + 9*b := by
    have hbackend : (0 : ℝ) ≤ ((a)^3) + ((2)*((a)^2)) + ((-1)*(16)*(a)*(b)) + (a) + ((b)^3) + ((6)*((b)^2)) + ((9)*(b)) := by
      have hgg1 : (0 : ℝ) ≤ a := by first | positivity | nlinarith
      have hsg1 : (0 : ℝ) ≤ (1/1)*(1 - (1/4)*a - (1/4)*b)^2 + (80/147)*(-(21/16)*a + (147/80)*b)^2 + (0/1)*(0/1)^2 := by positivity
      have hpg1 := mul_nonneg hsg1 hgg1
      have hgg2 : (0 : ℝ) ≤ b := by first | positivity | nlinarith
      have hsg2 : (0 : ℝ) ≤ (1/9)*((9/1) - (17/4)*a + (11/20)*b)^2 + (3600/3479)*(-(497/720)*a + (3479/3600)*b)^2 + (0/1)*(0/1)^2 := by positivity
      have hpg2 := mul_nonneg hsg2 hgg2
      have hs0 : (0 : ℝ) ≤ (10/49)*(-(7/2)*a + (49/10)*b)^2 + (0/1)*(0)^2 := by positivity
      have hid : (((a)^3) + ((2)*((a)^2)) + ((-1)*(16)*(a)*(b)) + (a) + ((b)^3) + ((6)*((b)^2)) + ((9)*(b))) = (((10/49)*(-(7/2)*a + (49/10)*b)^2 + (0/1)*(0)^2) + ((1/1)*(1 - (1/4)*a - (1/4)*b)^2 + (80/147)*(-(21/16)*a + (147/80)*b)^2 + (0/1)*(0/1)^2)*(a) + ((1/9)*((9/1) - (17/4)*a + (11/20)*b)^2 + (3600/3479)*(-(497/720)*a + (3479/3600)*b)^2 + (0/1)*(0/1)^2)*(b)) := by ring
      rw [hid]
      linarith
    convert hbackend using 1 <;> ring
  change _ ≤ _
  rw [← sub_nonneg]
  have hden1_pos : 0 < b := by
    first
    | positivity
    | nlinarith [ha, hb]
  have hden1_ne : b ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < a := by
    first
    | positivity
    | nlinarith [ha, hb]
  have hden2_ne : a ≠ 0 := ne_of_gt hden2_pos
  have hden : (0 : ℝ) < a*b := by positivity
  have hfrac : (-16 + (a + 1)^2/b + (b + 3)^2/a) = (a^3 + 2*a^2 - 16*a*b + a + b^3 + 6*b^2 + 9*b) / (a*b) := by
    field_simp
    <;> ring
  have hgoal : (0 : ℝ) ≤ -16 + (a + 1)^2/b + (b + 3)^2/a := by
    rw [hfrac]
    exact div_nonneg hnum (le_of_lt hden)
  convert hgoal using 1 <;> field_simp <;> ring



theorem real_p48 (a b : ℝ) (ha : a > 0) (hb : b > 0) : (a + 1)^2 / b + (b + 3)^2 / a ≥ 16 := by
  exact @real_p48' a b ha hb
