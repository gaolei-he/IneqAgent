import Mathlib

open Real

theorem P33 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : 1 + sqrt (a * b) + sqrt (b * c) + sqrt (c * a) ≤ sqrt (a * b + c) + sqrt (b * c + a) + sqrt (c * a + b) := by
  have hab_nonneg : 0 ≤ a * b := by positivity
  have hbc_nonneg : 0 ≤ b * c := by positivity
  have hca_nonneg : 0 ≤ c * a := by positivity
  have hab_amgm : 2 * sqrt (a * b) ≤ a + b := by
    have hsqrt_sq : sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt hab_nonneg
    nlinarith [sq_nonneg (a - b), sqrt_nonneg (a * b)]
  have hbc_amgm : 2 * sqrt (b * c) ≤ b + c := by
    have hsqrt_sq : sqrt (b * c) ^ 2 = b * c := Real.sq_sqrt hbc_nonneg
    nlinarith [sq_nonneg (b - c), sqrt_nonneg (b * c)]
  have hca_amgm : 2 * sqrt (c * a) ≤ c + a := by
    have hsqrt_sq : sqrt (c * a) ^ 2 = c * a := Real.sq_sqrt hca_nonneg
    nlinarith [sq_nonneg (c - a), sqrt_nonneg (c * a)]
  have h1 : sqrt (a * b) + c ≤ sqrt (a * b + c) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    have hsqrt_sq : sqrt (a * b) ^ 2 = a * b := Real.sq_sqrt hab_nonneg
    nlinarith [hab_amgm, h, hc]
  have h2 : sqrt (b * c) + a ≤ sqrt (b * c + a) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    have hsqrt_sq : sqrt (b * c) ^ 2 = b * c := Real.sq_sqrt hbc_nonneg
    nlinarith [hbc_amgm, h, ha]
  have h3 : sqrt (c * a) + b ≤ sqrt (c * a + b) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    have hsqrt_sq : sqrt (c * a) ^ 2 = c * a := Real.sq_sqrt hca_nonneg
    nlinarith [hca_amgm, h, hb]
  have hleft : 1 + sqrt (a * b) + sqrt (b * c) + sqrt (c * a) =
      (sqrt (a * b) + c) + (sqrt (b * c) + a) + (sqrt (c * a) + b) := by
    nlinarith [h]
  rw [hleft]
  linarith
