import Mathlib

theorem real_p11 (x y : ℝ) (hx : x > 0) (hy : y > 0) (h : x + 2 * y = 5) : (x + 1) * (2 * y + 1) / √(x * y) ≥ 4 * √3 := by
  have hx_eq : x = 5 - 2 * y := by linarith
  let A : ℝ := (x + 1) * (2 * y + 1)
  have hxy_pos : 0 < x * y := by positivity
  have hnum_pos : 0 < A := by
    dsimp [A]
    positivity
  have hden_pos : 0 < Real.sqrt (x * y) := by
    exact Real.sqrt_pos.2 hxy_pos
  have hsq_bound : 48 * (x * y) ≤ A ^ 2 := by
    have hfac :
        48 * (x * y) + 4 * (y - 1) ^ 2 * (2 * y - 3) ^ 2 = A ^ 2 := by
      dsimp [A]
      rw [hx_eq]
      ring
    have hsqfac : 0 ≤ 4 * (y - 1) ^ 2 * (2 * y - 3) ^ 2 := by positivity
    nlinarith
  have hdiv_bound : 48 ≤ A ^ 2 / (x * y) := by
    rw [le_div_iff₀ hxy_pos]
    exact hsq_bound
  have hsqrt_sq : (Real.sqrt (x * y)) ^ 2 = x * y := by
    exact Real.sq_sqrt (le_of_lt hxy_pos)
  have hleft_sq : (4 * Real.sqrt 3) ^ 2 ≤ (A / Real.sqrt (x * y)) ^ 2 := by
    have hsqrt3_sq : (Real.sqrt 3) ^ 2 = 3 := by
      rw [Real.sq_sqrt]
      norm_num
    calc
      (4 * Real.sqrt 3) ^ 2 = 4 ^ 2 * (Real.sqrt 3) ^ 2 := by ring
      _ = 48 := by
        rw [hsqrt3_sq]
        norm_num
      _ ≤ A ^ 2 / (x * y) := hdiv_bound
      _ = (A / Real.sqrt (x * y)) ^ 2 := by
        rw [div_pow, hsqrt_sq]
  have hleft_nonneg : 0 ≤ A / Real.sqrt (x * y) := by
    positivity
  change A / Real.sqrt (x * y) ≥ 4 * Real.sqrt 3
  exact le_of_sq_le_sq hleft_sq hleft_nonneg
