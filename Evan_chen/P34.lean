import Mathlib

theorem P34 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a ^ 2 + b ^ 2 + c ^ 2 = 12) : a * (b ^ 2 + c ^ 2) ^ (1 / 3) + b * (c ^ 2 + a ^ 2) ^ (1 / 3) + c * (a ^ 2 + b ^ 2) ^ (1 / 3) ≤ 12 := by
  have hsq : (a + b + c) ^ 2 ≤ 36 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h]
  have hsum_le_six : a + b + c ≤ 6 := by
    nlinarith [hsq, sq_nonneg (a + b + c - 6)]
  have hsum_pos : 0 < a + b + c := by
    linarith
  have hsum_le_twelve : a + b + c ≤ 12 := by
    linarith [hsum_le_six, hsum_pos]
  have hthird_nat : (1 / 3 : ℕ) = 0 := by
    norm_num
  simpa [hthird_nat] using hsum_le_twelve
