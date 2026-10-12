import Mathlib

theorem real_p47 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b + b * c + c * a = 1) : √(3 * a^2 + b^2) / (a * b) + √(3 * b^2 + c^2) / (b * c) + √(3 * c^2 + a^2) / (c * a) ≥ 6 * √3 := by
  set L :=
    Real.sqrt (3 * a ^ 2 + b ^ 2) / (a * b) + Real.sqrt (3 * b ^ 2 + c ^ 2) / (b * c) +
      Real.sqrt (3 * c ^ 2 + a ^ 2) / (c * a)
  -- All products of two variables are positive, hence nonzero.
  have hab : 0 < a * b := mul_pos ha hb
  have hbc : 0 < b * c := mul_pos hb hc
  have hca : 0 < c * a := mul_pos hc ha
  have habc : 0 < a * b * c := mul_pos hab hc
  have hab_ne : a * b ≠ 0 := ne_of_gt hab
  have hbc_ne : b * c ≠ 0 := ne_of_gt hbc
  have hca_ne : c * a ≠ 0 := ne_of_gt hca
  -- Quadratic lower bounds for each square root: √(3x^2 + y^2) ≥ (3x + y) / 2.
  have hs1 : (3 * a + b) / 2 ≤ Real.sqrt (3 * a ^ 2 + b ^ 2) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    nlinarith [sq_nonneg (a - b)]
  have hs2 : (3 * b + c) / 2 ≤ Real.sqrt (3 * b ^ 2 + c ^ 2) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    nlinarith [sq_nonneg (b - c)]
  have hs3 : (3 * c + a) / 2 ≤ Real.sqrt (3 * c ^ 2 + a ^ 2) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    nlinarith [sq_nonneg (c - a)]
  -- Multiply each bound by the positive variable needed for the common denominator.
  have hm1 : c * ((3 * a + b) / 2) ≤ c * Real.sqrt (3 * a ^ 2 + b ^ 2) := by
    exact mul_le_mul_of_nonneg_left hs1 (le_of_lt hc)
  have hm2 : a * ((3 * b + c) / 2) ≤ a * Real.sqrt (3 * b ^ 2 + c ^ 2) := by
    exact mul_le_mul_of_nonneg_left hs2 (le_of_lt ha)
  have hm3 : b * ((3 * c + a) / 2) ≤ b * Real.sqrt (3 * c ^ 2 + a ^ 2) := by
    exact mul_le_mul_of_nonneg_left hs3 (le_of_lt hb)
  -- Summing and using ab + bc + ca = 1 gives L * (abc) ≥ 2.
  have hmul_lower :
      2 ≤ c * Real.sqrt (3 * a ^ 2 + b ^ 2) + a * Real.sqrt (3 * b ^ 2 + c ^ 2) +
          b * Real.sqrt (3 * c ^ 2 + a ^ 2) := by
    nlinarith [hm1, hm2, hm3, h]
  have hLmul : 2 ≤ L * (a * b * c) := by
    have hEq :
        L * (a * b * c) =
          c * Real.sqrt (3 * a ^ 2 + b ^ 2) + a * Real.sqrt (3 * b ^ 2 + c ^ 2) +
            b * Real.sqrt (3 * c ^ 2 + a ^ 2) := by
      unfold L
      field_simp [hab_ne, hbc_ne, hca_ne]
    nlinarith [hmul_lower, hEq]
  -- AM-GM on ab, bc, ca (with sum 1) bounds the product by 1/27.
  have h_amgm0 :
      (a * b) ^ (1 / (3 : ℝ)) * (b * c) ^ (1 / (3 : ℝ)) * (c * a) ^ (1 / (3 : ℝ))
        ≤ (1 / (3 : ℝ)) * (a * b) + (1 / (3 : ℝ)) * (b * c) + (1 / (3 : ℝ)) * (c * a) := by
    exact Real.geom_mean_le_arith_mean3_weighted
      (by norm_num) (by norm_num) (by norm_num)
      (le_of_lt hab) (le_of_lt hbc) (le_of_lt hca)
      (by norm_num)
  have h_amgm : (a * b * (b * c) * (c * a)) ^ (1 / (3 : ℝ)) ≤ 1 / 3 := by
    have hEq1 :
        (a * b) ^ (1 / (3 : ℝ)) * (b * c) ^ (1 / (3 : ℝ)) * (c * a) ^ (1 / (3 : ℝ)) =
          (a * b * (b * c) * (c * a)) ^ (1 / (3 : ℝ)) := by
      calc
        (a * b) ^ (1 / (3 : ℝ)) * (b * c) ^ (1 / (3 : ℝ)) * (c * a) ^ (1 / (3 : ℝ))
          = ((a * b) * (b * c)) ^ (1 / (3 : ℝ)) * (c * a) ^ (1 / (3 : ℝ)) := by
              rw [← Real.mul_rpow (le_of_lt hab) (le_of_lt hbc)]
        _ = (a * b * (b * c) * (c * a)) ^ (1 / (3 : ℝ)) := by
              symm
              exact Real.mul_rpow (by positivity) (le_of_lt hca)
    calc
      (a * b * (b * c) * (c * a)) ^ (1 / (3 : ℝ)) =
          (a * b) ^ (1 / (3 : ℝ)) * (b * c) ^ (1 / (3 : ℝ)) * (c * a) ^ (1 / (3 : ℝ)) := by
            symm
            exact hEq1
      _ ≤ (1 / (3 : ℝ)) * (a * b) + (1 / (3 : ℝ)) * (b * c) + (1 / (3 : ℝ)) * (c * a) := h_amgm0
      _ = 1 / 3 := by nlinarith [h]
  have hprod_le : a * b * (b * c) * (c * a) ≤ 1 / 27 := by
    have hcube := Real.rpow_le_rpow (by positivity) h_amgm (by norm_num : 0 ≤ (3 : ℝ))
    have hleft :
        ((a * b * (b * c) * (c * a)) ^ (1 / (3 : ℝ))) ^ (3 : ℝ) =
          a * b * (b * c) * (c * a) := by
      simpa using
        (Real.rpow_mul (by positivity : 0 ≤ a * b * (b * c) * (c * a)) (1 / (3 : ℝ)) (3 : ℝ)).symm
    have hright : (1 / (3 : ℝ)) ^ (3 : ℝ) = 1 / 27 := by norm_num
    rw [hleft, hright] at hcube
    exact hcube
  have habc_sq_le : (a * b * c) ^ 2 ≤ 1 / 27 := by
    have hEq : a * b * (b * c) * (c * a) = (a * b * c) ^ 2 := by ring
    nlinarith [hprod_le, hEq]
  -- Convert (abc)^2 ≤ 1/27 into 6√3 * abc ≤ 2, then divide by the positive abc.
  have habc_bound : 6 * Real.sqrt 3 * (a * b * c) ≤ 2 := by
    nlinarith [habc_sq_le, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have htarget_mul : 6 * Real.sqrt 3 * (a * b * c) ≤ L * (a * b * c) := by
    nlinarith [hLmul, habc_bound]
  have hfinal : 6 * Real.sqrt 3 ≤ L := by
    exact le_of_mul_le_mul_right htarget_mul habc
  simpa [L] using hfinal
