import Mathlib

theorem real_p44 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b + b * c + c * a = 3) : 1 / (1 + a^2 * (b + c)) + 1 / (1 + b^2 * (c + a)) + 1 / (1 + c^2 * (a + b)) ≤ 1 / (a * b * c) := by
  have habc_pos : 0 < a * b * c := by positivity
  have habc_le_one : a * b * c ≤ 1 := by
    have hs1 : 0 ≤ ((a*b) - (b*c))^2 := sq_nonneg _
    have hs2 : 0 ≤ ((b*c) - (c*a))^2 := sq_nonneg _
    have hs3 : 0 ≤ ((c*a) - (a*b))^2 := sq_nonneg _
    have hs2le : (a*b)*(b*c) + (b*c)*(c*a) + (c*a)*(a*b) ≤ 3 := by
      nlinarith [hs1, hs2, hs3, h]
    have hschur_sq : 0 ≤ (a*b)*((b*c)-(c*a))^2 + (b*c)*((c*a)-(a*b))^2 + (c*a)*((a*b)-(b*c))^2 := by positivity
    have hschur : 9*(a*b)*(b*c)*(c*a) ≤ 3*((a*b)*(b*c) + (b*c)*(c*a) + (c*a)*(a*b)) := by
      nlinarith [hschur_sq, h]
    have hsq : (a*b*c)^2 ≤ (1:ℝ)^2 := by
      nlinarith [hschur, hs2le]
    exact le_of_sq_le_sq hsq (by norm_num)
  have hden1 : 1 + a^2*(b+c) = 1 + 3*a - a*b*c := by
    nlinarith [h]
  have hd1pos : 0 < 1 + a^2*(b+c) := by
    rw [hden1]
    nlinarith [ha, habc_le_one]
  have h3apos : 0 < 3*a := by nlinarith [ha]
  have hterm1 : 1/(1 + a^2*(b+c)) ≤ 1/(3*a) := by
    apply one_div_le_one_div_of_le h3apos
    rw [hden1]
    nlinarith [habc_le_one]
  have hden2 : 1 + b^2*(c+a) = 1 + 3*b - a*b*c := by
    nlinarith [h]
  have hd2pos : 0 < 1 + b^2*(c+a) := by
    rw [hden2]
    nlinarith [hb, habc_le_one]
  have h3bpos : 0 < 3*b := by nlinarith [hb]
  have hterm2 : 1/(1 + b^2*(c+a)) ≤ 1/(3*b) := by
    apply one_div_le_one_div_of_le h3bpos
    rw [hden2]
    nlinarith [habc_le_one]
  have hden3 : 1 + c^2*(a+b) = 1 + 3*c - a*b*c := by
    nlinarith [h]
  have hd3pos : 0 < 1 + c^2*(a+b) := by
    rw [hden3]
    nlinarith [hc, habc_le_one]
  have h3cpos : 0 < 3*c := by nlinarith [hc]
  have hterm3 : 1/(1 + c^2*(a+b)) ≤ 1/(3*c) := by
    apply one_div_le_one_div_of_le h3cpos
    rw [hden3]
    nlinarith [habc_le_one]
  have hsum : 1/(3*a) + 1/(3*b) + 1/(3*c) = 1/(a*b*c) := by
    field_simp [ha.ne', hb.ne', hc.ne', habc_pos.ne']
    nlinarith [h]
  calc
    1 / (1 + a^2 * (b + c)) + 1 / (1 + b^2 * (c + a)) + 1 / (1 + c^2 * (a + b))
        ≤ 1/(3*a) + 1/(3*b) + 1/(3*c) := by
          gcongr
    _ = 1/(a*b*c) := hsum
