import Mathlib

theorem P11 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hp : a * b + a * c + b * c = a * b * c) (hq : 27 ≤ a * b * c) : 64 ≤ (a + 1) * (b + 1) * (c + 1) := by
  have habc_pos : 0 < a * b * c := by positivity
  have h_expand : (a + 1) * (b + 1) * (c + 1) = 2 * (a * b * c) + (a + b + c) + 1 := by
    calc
      (a + 1) * (b + 1) * (c + 1)
          = a * b * c + (a * b + a * c + b * c) + a + b + c + 1 := by ring
      _ = a * b * c + a * b * c + a + b + c + 1 := by rw [hp]
      _ = 2 * (a * b * c) + (a + b + c) + 1 := by ring
  have h_sos : 0 ≤ (a + b + c) * (a * b + a * c + b * c) - 9 * (a * b * c) := by
    have hid : (a + b + c) * (a * b + a * c + b * c) - 9 * (a * b * c)
        = a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 := by ring
    rw [hid]
    positivity
  have h_nonneg_mul : 0 ≤ (a + b + c - 9) * (a * b * c) := by
    have hEq : (a + b + c - 9) * (a * b * c)
        = (a + b + c) * (a * b + a * c + b * c) - 9 * (a * b * c) := by
      rw [hp]
      ring
    rw [hEq]
    exact h_sos
  have hsum_ge_nine : 9 ≤ a + b + c := by
    have h_nonneg_factor : 0 ≤ a + b + c - 9 := by
      exact (mul_nonneg_iff_of_pos_right habc_pos).mp h_nonneg_mul
    linarith
  have h2abc_ge : 54 ≤ 2 * (a * b * c) := by nlinarith
  rw [h_expand]
  nlinarith
