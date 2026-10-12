import Mathlib

theorem real_p40 (x y : ℝ) (hx : x^2 ≤ 1) (hy : y^2 ≤ 1) : x * √(1 - y^2) + y * √(1 - x^2) ≤ 1 := by
  let p : ℝ := √(1 - y^2)
  let q : ℝ := √(1 - x^2)
  have hp_sq : p ^ 2 = 1 - y ^ 2 := by
    dsimp [p]
    rw [Real.sq_sqrt]
    nlinarith
  have hq_sq : q ^ 2 = 1 - x ^ 2 := by
    dsimp [q]
    rw [Real.sq_sqrt]
    nlinarith
  -- Cauchy-Schwarz step: (x p + y q)^2 ≤ (x^2 + y^2)(p^2 + q^2)
  have hprod : (x * p + y * q) ^ 2 ≤ (x ^ 2 + y ^ 2) * (p ^ 2 + q ^ 2) := by
    nlinarith [sq_nonneg (x * q - y * p)]
  -- Since p^2 = 1 - y^2 and q^2 = 1 - x^2, the right-hand side is s(2-s) ≤ 1.
  have hsumsq : p ^ 2 + q ^ 2 = 2 - x ^ 2 - y ^ 2 := by
    nlinarith
  have hEsq : (x * p + y * q) ^ 2 ≤ 1 := by
    nlinarith [hprod, hsumsq, sq_nonneg (x ^ 2 + y ^ 2 - 1)]
  -- From (x p + y q)^2 ≤ 1 conclude x p + y q ≤ 1.
  by_cases hle : x * p + y * q ≤ 1
  · simpa [p, q] using hle
  · nlinarith
