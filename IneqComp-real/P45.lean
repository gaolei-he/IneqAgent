import Mathlib

theorem real_p45 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    a + b + c - 3 * (a * b * c) ^ (3⁻¹: ℝ) ≥ a + b - 2 * √(a * b) := by
  have hab0 : 0 ≤ a * b := mul_nonneg (le_of_lt ha) (le_of_lt hb)
  have hs0 : 0 ≤ √(a * b) := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := le_of_lt hc
  have hsqrt_mul : √(a * b) * √(a * b) = a * b := Real.mul_self_sqrt hab0
  have hw : (3⁻¹ : ℝ) + (3⁻¹ : ℝ) + (3⁻¹ : ℝ) = 1 := by norm_num
  have hgm := Real.geom_mean_le_arith_mean3_weighted
      (w₁ := (3⁻¹ : ℝ)) (w₂ := (3⁻¹ : ℝ)) (w₃ := (3⁻¹ : ℝ))
      (p₁ := c) (p₂ := √(a * b)) (p₃ := √(a * b))
      (by norm_num : 0 ≤ (3⁻¹ : ℝ)) (by norm_num : 0 ≤ (3⁻¹ : ℝ))
      (by norm_num : 0 ≤ (3⁻¹ : ℝ)) hc0 hs0 hs0 hw
  have hprod_of_sqrt :
      c ^ (3⁻¹ : ℝ) * (√(a * b)) ^ (3⁻¹ : ℝ) * (√(a * b)) ^ (3⁻¹ : ℝ)
        = (a * b * c) ^ (3⁻¹ : ℝ) := by
    calc
      c ^ (3⁻¹ : ℝ) * (√(a * b)) ^ (3⁻¹ : ℝ) * (√(a * b)) ^ (3⁻¹ : ℝ)
          = c ^ (3⁻¹ : ℝ) * ((√(a * b)) ^ (3⁻¹ : ℝ) * (√(a * b)) ^ (3⁻¹ : ℝ)) := by
            ring
      _ = c ^ (3⁻¹ : ℝ) * ((√(a * b) * √(a * b)) ^ (3⁻¹ : ℝ)) := by
            rw [Real.mul_rpow hs0 hs0]
      _ = (c * (√(a * b) * √(a * b))) ^ (3⁻¹ : ℝ) := by
            rw [Real.mul_rpow hc0 (mul_nonneg hs0 hs0)]
      _ = (a * b * c) ^ (3⁻¹ : ℝ) := by
            have hbase : c * (√(a * b) * √(a * b)) = a * b * c := by
              rw [hsqrt_mul]
              ring
            exact congrArg (fun t : ℝ => t ^ (3⁻¹ : ℝ)) hbase
  have hgm' :
      (a * b * c) ^ (3⁻¹ : ℝ)
        ≤ (3⁻¹ : ℝ) * c + (3⁻¹ : ℝ) * √(a * b) + (3⁻¹ : ℝ) * √(a * b) := by
    simpa [hprod_of_sqrt] using hgm
  have h2 : 3 * (a * b * c) ^ (3⁻¹ : ℝ) ≤ c + 2 * √(a * b) := by
    have hmul :
        3 * ((a * b * c) ^ (3⁻¹ : ℝ))
          ≤ 3 * ((3⁻¹ : ℝ) * c + (3⁻¹ : ℝ) * √(a * b) + (3⁻¹ : ℝ) * √(a * b)) := by
          exact mul_le_mul_of_nonneg_left hgm' (by norm_num : (0 : ℝ) ≤ 3)
    have hRHS :
        3 * ((3⁻¹ : ℝ) * c + (3⁻¹ : ℝ) * √(a * b) + (3⁻¹ : ℝ) * √(a * b))
          = c + 2 * √(a * b) := by
          ring_nf
    simpa [hRHS] using hmul
  nlinarith [h2]
