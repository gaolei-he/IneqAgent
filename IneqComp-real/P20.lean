import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem real_p20' (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : a^2 / b + b^2 / c + c^2 / a ≥ a + b + c + 4 * (a - b)^2 / (a + b + c) := by
  have hnum : (0 : ℝ) ≤ a^4*c - 4*a^3*b*c + a^3*c^2 + a^2*b^3 + 6*a^2*b^2*c - 2*a^2*b*c^2 + a*b^4 - 4*a*b^3*c - 2*a*b^2*c^2 + b^2*c^3 + b*c^4 := by
    have hbackend : (0 : ℝ) ≤ (((a)^4)*(c)) + ((-1)*(4)*((a)^3)*(b)*(c)) + (((a)^3)*((c)^2)) + (((a)^2)*((b)^3)) + ((6)*((a)^2)*((b)^2)*(c)) + ((-1)*(2)*((a)^2)*(b)*((c)^2)) + ((a)*((b)^4)) + ((-1)*(4)*(a)*((b)^3)*(c)) + ((-1)*(2)*(a)*((b)^2)*((c)^2)) + (((b)^2)*((c)^3)) + ((b)*((c)^4)) := by
      have hgg1 : (0 : ℝ) ≤ a := by first | positivity | nlinarith
      have hsg1 : (0 : ℝ) ≤ (1/4)*(-(2/1)*a*c - (2/1)*(b^2) + (4/1)*b*c)^2 + (0/1)*(0)^2 + (0/1)*(0)^2 := by positivity
      have hpg1 := mul_nonneg hsg1 hgg1
      have hgg2 : (0 : ℝ) ≤ b := by first | positivity | nlinarith
      have hsg2 : (0 : ℝ) ≤ (1/1)*(-a*b + c^2)^2 + (0/1)*(0)^2 := by positivity
      have hpg2 := mul_nonneg hsg2 hgg2
      have hgg3 : (0 : ℝ) ≤ c := by first | positivity | nlinarith
      have hsg3 : (0 : ℝ) ≤ (1/1)*(a^2 - (2/1)*a*b + b*c)^2 + (0/1)*(0)^2 + (0/1)*(0)^2 := by positivity
      have hpg3 := mul_nonneg hsg3 hgg3
      have hs0 : (0 : ℝ) ≤ (0)*(1)^2 := by positivity
      have hid : ((((a)^4)*(c)) + ((-1)*(4)*((a)^3)*(b)*(c)) + (((a)^3)*((c)^2)) + (((a)^2)*((b)^3)) + ((6)*((a)^2)*((b)^2)*(c)) + ((-1)*(2)*((a)^2)*(b)*((c)^2)) + ((a)*((b)^4)) + ((-1)*(4)*(a)*((b)^3)*(c)) + ((-1)*(2)*(a)*((b)^2)*((c)^2)) + (((b)^2)*((c)^3)) + ((b)*((c)^4))) = (((0)*(1)^2) + ((1/4)*(-(2/1)*a*c - (2/1)*(b^2) + (4/1)*b*c)^2 + (0/1)*(0)^2 + (0/1)*(0)^2)*(a) + ((1/1)*(-a*b + c^2)^2 + (0/1)*(0)^2)*(b) + ((1/1)*(a^2 - (2/1)*a*b + b*c)^2 + (0/1)*(0)^2 + (0/1)*(0)^2)*(c)) := by ring
      rw [hid]
      linarith
    convert hbackend using 1 <;> ring
  change _ ≤ _
  rw [← sub_nonneg]
  have hden1_pos : 0 < a := by
    first
    | positivity
    | nlinarith [ha, hb, hc]
  have hden1_ne : a ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < b := by
    first
    | positivity
    | nlinarith [ha, hb, hc]
  have hden2_ne : b ≠ 0 := ne_of_gt hden2_pos
  have hden3_pos : 0 < c := by
    first
    | positivity
    | nlinarith [ha, hb, hc]
  have hden3_ne : c ≠ 0 := ne_of_gt hden3_pos
  have hden4_pos : 0 < a + b + c := by
    first
    | positivity
    | nlinarith [ha, hb, hc]
  have hden4_ne : a + b + c ≠ 0 := ne_of_gt hden4_pos
  have hden : (0 : ℝ) < a^2*b*c + a*b^2*c + a*b*c^2 := by positivity
  have hfrac : (a^2/b - a + b^2/c - b - c - 4*(a - b)^2/(a + b + c) + c^2/a) = (a^4*c - 4*a^3*b*c + a^3*c^2 + a^2*b^3 + 6*a^2*b^2*c - 2*a^2*b*c^2 + a*b^4 - 4*a*b^3*c - 2*a*b^2*c^2 + b^2*c^3 + b*c^4) / (a^2*b*c + a*b^2*c + a*b*c^2) := by
    field_simp
    <;> ring
  have hgoal : (0 : ℝ) ≤ a^2/b - a + b^2/c - b - c - 4*(a - b)^2/(a + b + c) + c^2/a := by
    rw [hfrac]
    exact div_nonneg hnum (le_of_lt hden)
  convert hgoal using 1 <;> field_simp <;> ring



theorem real_p20 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) : a^2 / b + b^2 / c + c^2 / a ≥ a + b + c + 4 * (a - b)^2 / (a + b + c) := by
  exact @real_p20' a b c ha hb hc hab hbc hca
