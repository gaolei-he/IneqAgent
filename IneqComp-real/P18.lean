import Mathlib

private lemma sqrt5_linear_lower_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + 2 * b) / √(5 : ℝ) ≤ √(a ^ 2 + b ^ 2) := by
  have hsqrt5_pos : 0 < √(5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hlin_nonneg : 0 ≤ (a + 2 * b) / √(5 : ℝ) := by positivity
  have hrad_nonneg : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  apply (Real.le_sqrt hlin_nonneg hrad_nonneg).2
  have hsq : ((a + 2 * b) / √(5 : ℝ)) ^ 2 = (a + 2 * b) ^ 2 / 5 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  rw [hsq]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 5)]
  nlinarith [sq_nonneg (2 * a - b)]

theorem real_p18 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (√(x^2 + y^2) + √(y^2 + 4 * z^2) + √(z^2 + 16 * x^2)) / (9 * x + 3 * y + 5 * z) ≥ √5 / 5 := by
  have hx0 : 0 ≤ x := le_of_lt hx
  have hy0 : 0 ≤ y := le_of_lt hy
  have hz0 : 0 ≤ z := le_of_lt hz
  have hden_pos : 0 < 9 * x + 3 * y + 5 * z := by positivity
  have hsqrt5_ne : √(5 : ℝ) ≠ 0 := by positivity
  have h1 : (x + 2 * y) / √(5 : ℝ) ≤ √(x ^ 2 + y ^ 2) := by
    exact sqrt5_linear_lower_bound x y hx0 hy0
  have h2 : (y + 4 * z) / √(5 : ℝ) ≤ √(y ^ 2 + 4 * z ^ 2) := by
    have h2z0 : 0 ≤ 2 * z := by positivity
    convert sqrt5_linear_lower_bound y (2 * z) hy0 h2z0 using 1 <;> ring_nf
  have h3 : (z + 8 * x) / √(5 : ℝ) ≤ √(z ^ 2 + 16 * x ^ 2) := by
    have h4x0 : 0 ≤ 4 * x := by positivity
    convert sqrt5_linear_lower_bound z (4 * x) hz0 h4x0 using 1 <;> ring_nf
  have hsum :
      (9 * x + 3 * y + 5 * z) / √(5 : ℝ) ≤
        √(x ^ 2 + y ^ 2) + √(y ^ 2 + 4 * z ^ 2) + √(z ^ 2 + 16 * x ^ 2) := by
    have hleft :
        (9 * x + 3 * y + 5 * z) / √(5 : ℝ) =
          (x + 2 * y) / √(5 : ℝ) + (y + 4 * z) / √(5 : ℝ) + (z + 8 * x) / √(5 : ℝ) := by
      field_simp [hsqrt5_ne]
      ring
    rw [hleft]
    exact add_le_add (add_le_add h1 h2) h3
  have htarget :
      (√(5 : ℝ) / 5) * (9 * x + 3 * y + 5 * z) ≤
        √(x ^ 2 + y ^ 2) + √(y ^ 2 + 4 * z ^ 2) + √(z ^ 2 + 16 * x ^ 2) := by
    have hcoef : √(5 : ℝ) / 5 = 1 / √(5 : ℝ) := by
      field_simp [hsqrt5_ne]
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    rw [hcoef]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsum
  rw [ge_iff_le]
  rw [div_eq_mul_inv]
  exact (le_mul_inv_iff₀ hden_pos).2 htarget
