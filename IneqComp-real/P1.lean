import Mathlib

lemma real_p1_first_eliminated_factor_nonneg (x y : ℝ) :
    0 ≤ x ^ 2 * y ^ 2 - x ^ 2 * y + x ^ 2 - x * y ^ 2 + x * y - 2 * x + y ^ 2 - 2 * y + 2 := by
  have hquad_pos : 0 < y ^ 2 - y + 1 := by
    nlinarith [sq_nonneg (y - 1 / 2)]
  have htail2_nonneg : 0 ≤ 3 * y ^ 2 - 4 * y + 4 := by
    nlinarith [sq_nonneg (y - 2 / 3)]
  have hidentity :
      4 * (y ^ 2 - y + 1) *
          (x ^ 2 * y ^ 2 - x ^ 2 * y + x ^ 2 - x * y ^ 2 + x * y - 2 * x + y ^ 2 - 2 * y + 2) =
        (2 * (y ^ 2 - y + 1) * x + (-y ^ 2 + y - 2)) ^ 2 +
          (y - 1) ^ 2 * (3 * y ^ 2 - 4 * y + 4) := by
    ring
  have hleft_nonneg :
      0 ≤ 4 * (y ^ 2 - y + 1) *
          (x ^ 2 * y ^ 2 - x ^ 2 * y + x ^ 2 - x * y ^ 2 + x * y - 2 * x + y ^ 2 - 2 * y + 2) := by
    rw [hidentity]
    positivity
  nlinarith

lemma real_p1_second_eliminated_factor_nonneg (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    0 ≤ x ^ 4 + x ^ 3 * y ^ 2 + x ^ 3 * y + x ^ 2 * y ^ 3 + x ^ 2 * y + x ^ 2 +
      x * y ^ 3 + x * y ^ 2 + 2 * x * y - 2 * x + y ^ 4 + y ^ 2 - 2 * y + 1 := by
  have hidentity :
      x ^ 4 + x ^ 3 * y ^ 2 + x ^ 3 * y + x ^ 2 * y ^ 3 + x ^ 2 * y + x ^ 2 +
          x * y ^ 3 + x * y ^ 2 + 2 * x * y - 2 * x + y ^ 4 + y ^ 2 - 2 * y + 1 =
        (x + y - 1) ^ 2 +
          (x ^ 4 + x ^ 3 * y ^ 2 + x ^ 3 * y + x ^ 2 * y ^ 3 + x ^ 2 * y +
            x * y ^ 3 + x * y ^ 2 + y ^ 4) := by
    ring
  rw [hidentity]
  positivity

theorem real_p1 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = z * y + y * x + x * z) : 1 / (x^2 + y + 1) + 1 / (y^2 + z + 1) + 1 / (z^2 + x + 1) ≤ 1 := by
  have hA_pos : 0 < x ^ 2 + y + 1 := by
    nlinarith [sq_nonneg x, hy]
  have hB_pos : 0 < y ^ 2 + z + 1 := by
    nlinarith [sq_nonneg y, hz]
  have hC_pos : 0 < z ^ 2 + x + 1 := by
    nlinarith [sq_nonneg z, hx]
  have hABC_pos :
      0 < (x ^ 2 + y + 1) * (y ^ 2 + z + 1) * (z ^ 2 + x + 1) := by
    positivity
  have h_shifted_condition :
      (x - 1) + (y - 1) + (z - 1) +
        (x - 1) * (y - 1) + (y - 1) * (z - 1) + (z - 1) * (x - 1) = 0 := by
    nlinarith [h]
  have hsum_ge_three : 3 ≤ x + y + z := by
    have hsum_pos : 0 < x + y + z := by
      linarith
    have hpairs_le : 3 * (z * y + y * x + x * z) ≤ (x + y + z) ^ 2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
    have hprod : 3 * (x + y + z) ≤ (x + y + z) ^ 2 := by
      nlinarith [h, hpairs_le]
    nlinarith [hsum_pos, hprod]
  have hxy_sum_gt_one : 1 < x + y := by
    by_contra hnot
    have hxy_le : x + y ≤ 1 := le_of_not_gt hnot
    have hx_lt_one : x < 1 := by linarith
    have hxy_lt_y : x * y < y := by nlinarith [hy, hx_lt_one]
    have hright_pos : 0 < x + y - x * y := by nlinarith
    have hleft_nonpos : z * (x + y - 1) ≤ 0 := by nlinarith [hz, hxy_le]
    have hprod_identity : z * (x + y - 1) = x + y - x * y := by
      nlinarith [h]
    nlinarith
  have hyz_sum_gt_one : 1 < y + z := by
    by_contra hnot
    have hyz_le : y + z ≤ 1 := le_of_not_gt hnot
    have hy_lt_one : y < 1 := by linarith
    have hyz_lt_z : y * z < z := by nlinarith [hz, hy_lt_one]
    have hright_pos : 0 < y + z - y * z := by nlinarith
    have hleft_nonpos : x * (y + z - 1) ≤ 0 := by nlinarith [hx, hyz_le]
    have hprod_identity : x * (y + z - 1) = y + z - y * z := by
      nlinarith [h]
    nlinarith
  have hzx_sum_gt_one : 1 < z + x := by
    by_contra hnot
    have hzx_le : z + x ≤ 1 := le_of_not_gt hnot
    have hz_lt_one : z < 1 := by linarith
    have hzx_lt_x : z * x < x := by nlinarith [hx, hz_lt_one]
    have hright_pos : 0 < z + x - z * x := by nlinarith
    have hleft_nonpos : y * (z + x - 1) ≤ 0 := by nlinarith [hy, hzx_le]
    have hprod_identity : y * (z + x - 1) = z + x - z * x := by
      nlinarith [h]
    nlinarith
  have hxy_minus_one_pos : 0 < x + y - 1 := by
    linarith
  have hyz_minus_one_pos : 0 < y + z - 1 := by
    linarith
  have hzx_minus_one_pos : 0 < z + x - 1 := by
    linarith
  have hz_mul_xy_minus_one : z * (x + y - 1) = x + y - x * y := by
    ring_nf at h ⊢
    linarith
  have hx_mul_yz_minus_one : x * (y + z - 1) = y + z - y * z := by
    ring_nf at h ⊢
    linarith
  have hy_mul_zx_minus_one : y * (z + x - 1) = z + x - z * x := by
    ring_nf at h ⊢
    linarith
  have hxy_sub_mul_pos : 0 < x + y - x * y := by
    rw [← hz_mul_xy_minus_one]
    positivity
  have hyz_sub_mul_pos : 0 < y + z - y * z := by
    rw [← hx_mul_yz_minus_one]
    positivity
  have hzx_sub_mul_pos : 0 < z + x - z * x := by
    rw [← hy_mul_zx_minus_one]
    positivity
  have h_from_cleared :
      (y ^ 2 + z + 1) * (z ^ 2 + x + 1) +
          (x ^ 2 + y + 1) * (z ^ 2 + x + 1) +
          (x ^ 2 + y + 1) * (y ^ 2 + z + 1) ≤
        (x ^ 2 + y + 1) * (y ^ 2 + z + 1) * (z ^ 2 + x + 1) →
      1 / (x ^ 2 + y + 1) + 1 / (y ^ 2 + z + 1) + 1 / (z ^ 2 + x + 1) ≤ 1 := by
    intro hclear
    have hsum_div :
        1 / (x ^ 2 + y + 1) + 1 / (y ^ 2 + z + 1) + 1 / (z ^ 2 + x + 1) =
          ((y ^ 2 + z + 1) * (z ^ 2 + x + 1) +
              (x ^ 2 + y + 1) * (z ^ 2 + x + 1) +
              (x ^ 2 + y + 1) * (y ^ 2 + z + 1)) /
            ((x ^ 2 + y + 1) * (y ^ 2 + z + 1) * (z ^ 2 + x + 1)) := by
      field_simp [ne_of_gt hA_pos, ne_of_gt hB_pos, ne_of_gt hC_pos]
    rw [hsum_div]
    exact div_le_one_of_le₀ hclear (le_of_lt hABC_pos)
  have hz_eq_fraction : z = (x + y - x * y) / (x + y - 1) := by
    rw [eq_div_iff (ne_of_gt hxy_minus_one_pos)]
    exact hz_mul_xy_minus_one
  let P : ℝ := x ^ 2 * y ^ 2 - x ^ 2 * y + x ^ 2 - x * y ^ 2 + x * y - 2 * x + y ^ 2 - 2 * y + 2
  let Q : ℝ :=
    x ^ 4 + x ^ 3 * y ^ 2 + x ^ 3 * y + x ^ 2 * y ^ 3 + x ^ 2 * y + x ^ 2 +
      x * y ^ 3 + x * y ^ 2 + 2 * x * y - 2 * x + y ^ 4 + y ^ 2 - 2 * y + 1
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact real_p1_first_eliminated_factor_nonneg x y
  have hQ_nonneg : 0 ≤ Q := by
    dsimp [Q]
    exact real_p1_second_eliminated_factor_nonneg x y hx hy
  have hPQ_nonneg : 0 ≤ P * Q := by
    positivity
  have hxy_minus_one_cube_pos : 0 < (x + y - 1) ^ 3 := by
    positivity
  have hcleared_gap_factor :
      (x + y - 1) ^ 3 *
          ((x ^ 2 + y + 1) * (y ^ 2 + z + 1) * (z ^ 2 + x + 1) -
            ((y ^ 2 + z + 1) * (z ^ 2 + x + 1) +
              (x ^ 2 + y + 1) * (z ^ 2 + x + 1) +
              (x ^ 2 + y + 1) * (y ^ 2 + z + 1))) =
        P * Q := by
    rw [hz_eq_fraction]
    dsimp [P, Q]
    field_simp [ne_of_gt hxy_minus_one_pos]
    ring
  have hcleared_gap_nonneg :
      0 ≤ (x ^ 2 + y + 1) * (y ^ 2 + z + 1) * (z ^ 2 + x + 1) -
          ((y ^ 2 + z + 1) * (z ^ 2 + x + 1) +
            (x ^ 2 + y + 1) * (z ^ 2 + x + 1) +
            (x ^ 2 + y + 1) * (y ^ 2 + z + 1)) := by
    refine nonneg_of_mul_nonneg_right ?_ hxy_minus_one_cube_pos
    rw [hcleared_gap_factor]
    exact hPQ_nonneg
  apply h_from_cleared
  exact sub_nonneg.mp hcleared_gap_nonneg
