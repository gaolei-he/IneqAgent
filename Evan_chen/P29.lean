import Mathlib

open Real

theorem P29 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 ≤ a / sqrt (a ^ 2 + 8 * b * c) + b / sqrt (b ^ 2 + 8 * a * c) + c / sqrt (c ^ 2 + 8 * a * b) := by
  have hrad_a_pos : 0 < a ^ 2 + 8 * b * c := by
    nlinarith [sq_nonneg a, mul_pos hb hc]
  have hrad_b_pos : 0 < b ^ 2 + 8 * a * c := by
    nlinarith [sq_nonneg b, mul_pos ha hc]
  have hrad_c_pos : 0 < c ^ 2 + 8 * a * b := by
    nlinarith [sq_nonneg c, mul_pos ha hb]
  have hsqrt_a_pos : 0 < sqrt (a ^ 2 + 8 * b * c) :=
    Real.sqrt_pos_of_pos hrad_a_pos
  have hsqrt_b_pos : 0 < sqrt (b ^ 2 + 8 * a * c) :=
    Real.sqrt_pos_of_pos hrad_b_pos
  have hsqrt_c_pos : 0 < sqrt (c ^ 2 + 8 * a * b) :=
    Real.sqrt_pos_of_pos hrad_c_pos
  have hsqrt_a_ne_zero : sqrt (a ^ 2 + 8 * b * c) ≠ 0 :=
    ne_of_gt hsqrt_a_pos
  have hsqrt_b_ne_zero : sqrt (b ^ 2 + 8 * a * c) ≠ 0 :=
    ne_of_gt hsqrt_b_pos
  have hsqrt_c_ne_zero : sqrt (c ^ 2 + 8 * a * b) ≠ 0 :=
    ne_of_gt hsqrt_c_pos
  have hterm_a_pos : 0 < a / sqrt (a ^ 2 + 8 * b * c) :=
    div_pos ha hsqrt_a_pos
  have hterm_b_pos : 0 < b / sqrt (b ^ 2 + 8 * a * c) :=
    div_pos hb hsqrt_b_pos
  have hterm_c_pos : 0 < c / sqrt (c ^ 2 + 8 * a * b) :=
    div_pos hc hsqrt_c_pos
  have ha_sq_pos : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb_sq_pos : 0 < b ^ 2 := sq_pos_of_pos hb
  have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_pos hc
  have hnorm_a_pos : 0 < 1 + 8 * (b * c / a ^ 2) := by
    have hdiv : 0 < b * c / a ^ 2 := div_pos (mul_pos hb hc) ha_sq_pos
    nlinarith
  have hnorm_b_pos : 0 < 1 + 8 * (a * c / b ^ 2) := by
    have hdiv : 0 < a * c / b ^ 2 := div_pos (mul_pos ha hc) hb_sq_pos
    nlinarith
  have hnorm_c_pos : 0 < 1 + 8 * (a * b / c ^ 2) := by
    have hdiv : 0 < a * b / c ^ 2 := div_pos (mul_pos ha hb) hc_sq_pos
    nlinarith
  have hnorm_prod : (b * c / a ^ 2) * (a * c / b ^ 2) * (a * b / c ^ 2) = 1 := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
  have hterm_a_norm :
      a / sqrt (a ^ 2 + 8 * b * c) = 1 / sqrt (1 + 8 * (b * c / a ^ 2)) := by
    have hrad_a_factor : a ^ 2 + 8 * b * c = a ^ 2 * (1 + 8 * (b * c / a ^ 2)) := by
      field_simp [ne_of_gt ha_sq_pos]
    have hsqrt_factor : sqrt (a ^ 2 + 8 * b * c) = a * sqrt (1 + 8 * (b * c / a ^ 2)) := by
      rw [hrad_a_factor]
      rw [Real.sqrt_mul (le_of_lt ha_sq_pos)]
      rw [Real.sqrt_sq (le_of_lt ha)]
    rw [hsqrt_factor]
    field_simp [ne_of_gt ha, ne_of_gt (Real.sqrt_pos_of_pos hnorm_a_pos)]
  have hterm_b_norm :
      b / sqrt (b ^ 2 + 8 * a * c) = 1 / sqrt (1 + 8 * (a * c / b ^ 2)) := by
    have hrad_b_factor : b ^ 2 + 8 * a * c = b ^ 2 * (1 + 8 * (a * c / b ^ 2)) := by
      field_simp [ne_of_gt hb_sq_pos]
    have hsqrt_factor : sqrt (b ^ 2 + 8 * a * c) = b * sqrt (1 + 8 * (a * c / b ^ 2)) := by
      rw [hrad_b_factor]
      rw [Real.sqrt_mul (le_of_lt hb_sq_pos)]
      rw [Real.sqrt_sq (le_of_lt hb)]
    rw [hsqrt_factor]
    field_simp [ne_of_gt hb, ne_of_gt (Real.sqrt_pos_of_pos hnorm_b_pos)]
  have hterm_c_norm :
      c / sqrt (c ^ 2 + 8 * a * b) = 1 / sqrt (1 + 8 * (a * b / c ^ 2)) := by
    have hrad_c_factor : c ^ 2 + 8 * a * b = c ^ 2 * (1 + 8 * (a * b / c ^ 2)) := by
      field_simp [ne_of_gt hc_sq_pos]
    have hsqrt_factor : sqrt (c ^ 2 + 8 * a * b) = c * sqrt (1 + 8 * (a * b / c ^ 2)) := by
      rw [hrad_c_factor]
      rw [Real.sqrt_mul (le_of_lt hc_sq_pos)]
      rw [Real.sqrt_sq (le_of_lt hc)]
    rw [hsqrt_factor]
    field_simp [ne_of_gt hc, ne_of_gt (Real.sqrt_pos_of_pos hnorm_c_pos)]
  have hweighted_cauchy {A B C : ℝ} :
      (a * A + b * B + c * C) ^ 2 ≤
        (a + b + c) * (a * A ^ 2 + b * B ^ 2 + c * C ^ 2) := by
    have h1 : 0 ≤ a * b * (A - B) ^ 2 := by positivity
    have h2 : 0 ≤ a * c * (A - C) ^ 2 := by positivity
    have h3 : 0 ≤ b * c * (B - C) ^ 2 := by positivity
    nlinarith
  have htitu {A B C : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
      (a + b + c) ^ 2 / (a * A + b * B + c * C) ≤ a / A + b / B + c / C := by
    have hden : 0 < a * A + b * B + c * C := by
      nlinarith [mul_pos ha hA, mul_pos hb hB, mul_pos hc hC]
    have hAne : A ≠ 0 := ne_of_gt hA
    have hBne : B ≠ 0 := ne_of_gt hB
    have hCne : C ≠ 0 := ne_of_gt hC
    rw [div_le_iff₀ hden]
    field_simp [hAne, hBne, hCne]
    have h1 : 0 ≤ a * b * C * (A - B) ^ 2 := by positivity
    have h2 : 0 ≤ a * c * B * (A - C) ^ 2 := by positivity
    have h3 : 0 ≤ b * c * A * (B - C) ^ 2 := by positivity
    nlinarith
  have hrad_weight_le_cube :
      a * (a ^ 2 + 8 * b * c) + b * (b ^ 2 + 8 * a * c) + c * (c ^ 2 + 8 * a * b) ≤
        (a + b + c) ^ 3 := by
    have h1 : 0 ≤ c * (a - b) ^ 2 := by positivity
    have h2 : 0 ≤ a * (b - c) ^ 2 := by positivity
    have h3 : 0 ≤ b * (a - c) ^ 2 := by positivity
    nlinarith
  have hsum_pos : 0 < a + b + c := by linarith
  have hden_pos :
      0 < a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
        c * sqrt (c ^ 2 + 8 * a * b) := by
    nlinarith [mul_pos ha hsqrt_a_pos, mul_pos hb hsqrt_b_pos, mul_pos hc hsqrt_c_pos]
  have hden_sq_le_sum_four :
      (a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
          c * sqrt (c ^ 2 + 8 * a * b)) ^ 2 ≤
        (a + b + c) ^ 4 := by
    have hcauchy := hweighted_cauchy (A := sqrt (a ^ 2 + 8 * b * c))
      (B := sqrt (b ^ 2 + 8 * a * c)) (C := sqrt (c ^ 2 + 8 * a * b))
    have hcauchy' :
        (a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
            c * sqrt (c ^ 2 + 8 * a * b)) ^ 2 ≤
          (a + b + c) *
            (a * (a ^ 2 + 8 * b * c) + b * (b ^ 2 + 8 * a * c) +
              c * (c ^ 2 + 8 * a * b)) := by
      simpa [Real.sq_sqrt hrad_a_pos.le, Real.sq_sqrt hrad_b_pos.le,
        Real.sq_sqrt hrad_c_pos.le] using hcauchy
    have hmul :
        (a + b + c) *
            (a * (a ^ 2 + 8 * b * c) + b * (b ^ 2 + 8 * a * c) +
              c * (c ^ 2 + 8 * a * b)) ≤
          (a + b + c) * (a + b + c) ^ 3 :=
      mul_le_mul_of_nonneg_left hrad_weight_le_cube hsum_pos.le
    calc
      (a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
          c * sqrt (c ^ 2 + 8 * a * b)) ^ 2
          ≤ (a + b + c) *
            (a * (a ^ 2 + 8 * b * c) + b * (b ^ 2 + 8 * a * c) +
              c * (c ^ 2 + 8 * a * b)) := hcauchy'
      _ ≤ (a + b + c) * (a + b + c) ^ 3 := hmul
      _ = (a + b + c) ^ 4 := by ring
  have hden_le_sum_sq :
      a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
        c * sqrt (c ^ 2 + 8 * a * b) ≤
        (a + b + c) ^ 2 := by
    have hden_sq_le_sum_sq_sq :
        (a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
            c * sqrt (c ^ 2 + 8 * a * b)) ^ 2 ≤
          ((a + b + c) ^ 2) ^ 2 := by
      calc
        (a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
            c * sqrt (c ^ 2 + 8 * a * b)) ^ 2
            ≤ (a + b + c) ^ 4 := hden_sq_le_sum_four
        _ = ((a + b + c) ^ 2) ^ 2 := by ring
    exact (sq_le_sq₀ hden_pos.le (sq_nonneg (a + b + c))).mp hden_sq_le_sum_sq_sq
  have hone_le_ratio :
      1 ≤ (a + b + c) ^ 2 /
        (a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
          c * sqrt (c ^ 2 + 8 * a * b)) := by
    rw [le_div_iff₀ hden_pos]
    simpa [one_mul] using hden_le_sum_sq
  have hratio_le_sum :
      (a + b + c) ^ 2 /
          (a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
            c * sqrt (c ^ 2 + 8 * a * b)) ≤
        a / sqrt (a ^ 2 + 8 * b * c) + b / sqrt (b ^ 2 + 8 * a * c) +
          c / sqrt (c ^ 2 + 8 * a * b) :=
    htitu hsqrt_a_pos hsqrt_b_pos hsqrt_c_pos
  exact hone_le_ratio.trans hratio_le_sum
