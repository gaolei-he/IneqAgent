import Mathlib

private lemma P7_sos {a b c : ℝ} (h : a * b * c = 1) :
    0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - (a + b + c) := by
  have ha1 : 0 ≤ (a - 1) ^ 2 := sq_nonneg (a - 1)
  have hb1 : 0 ≤ (b - 1) ^ 2 := sq_nonneg (b - 1)
  have hc1 : 0 ≤ (c - 1) ^ 2 := sq_nonneg (c - 1)
  have hab : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have hbc : 0 ≤ (b - c) ^ 2 := sq_nonneg (b - c)
  have hca : 0 ≤ (c - a) ^ 2 := sq_nonneg (c - a)
  have hab1 : 0 ≤ (a * b - 1) ^ 2 := sq_nonneg (a * b - 1)
  have hbc1 : 0 ≤ (b * c - 1) ^ 2 := sq_nonneg (b * c - 1)
  have hca1 : 0 ≤ (c * a - 1) ^ 2 := sq_nonneg (c * a - 1)
  nlinarith [ha1, hb1, hc1, hab, hbc, hca, hab1, hbc1, hca1, h]

theorem P7 {a b c : ℝ} (h : a * b * c = 1) : a + b + c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have hkey : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - (a + b + c) := P7_sos h
  linarith
