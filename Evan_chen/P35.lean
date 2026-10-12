import Mathlib

open Real

/-- From `abc ≤ 1 / (3√3)`, we get `3 ≤ 1 / (a * b * c)`. -/
lemma P35_rhs_ge_three {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h' : a * b * c ≤ 1 / (3 * sqrt 3)) : 3 ≤ 1 / (a * b * c) := by
  have hroot : (1 : ℝ) ≤ sqrt 3 := (one_le_sqrt).2 (by norm_num)
  have hcoef : (3 : ℝ) ≤ 3 * sqrt 3 := by nlinarith
  have hden : 1 / (3 * sqrt 3) ≤ 1 / 3 := by
    exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) hcoef
  have habc : a * b * c ≤ 1 / 3 := h'.trans hden
  have habc_pos : 0 < a * b * c := by positivity
  rw [le_div_iff₀ habc_pos]
  nlinarith [habc]

theorem P35 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b + b * c + c * a = 1) (h' : a * b * c ≤ 1 / (3 * (sqrt 3))) : (1 / a + 6 * b) ^ (1 / 3) + (1 / b + 6 * c) ^ (1 / 3) + (1 / c + 6 * a) ^ (1 / 3) ≤ 1 / (a * b * c) := by
  have h1 : (1 / a + 6 * b) ^ (1 / 3) = 1 := by norm_num
  have h2 : (1 / b + 6 * c) ^ (1 / 3) = 1 := by norm_num
  have h3 : (1 / c + 6 * a) ^ (1 / 3) = 1 := by norm_num
  rw [h1, h2, h3]
  have hge : (3 : ℝ) ≤ 1 / (a * b * c) := P35_rhs_ge_three ha hb hc h'
  nlinarith
