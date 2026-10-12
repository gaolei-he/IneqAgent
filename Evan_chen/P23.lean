import Mathlib

open Real

theorem P23 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / sqrt (a ^ 2 + 8 * b * c) + b / sqrt (b ^ 2 + 8 * a * c) + c / sqrt (c ^ 2 + 8 * a * b) ≤ 2 := by
  have hbc_pos : 0 < b * c := mul_pos hb hc
  have hac_pos : 0 < a * c := mul_pos ha hc
  have hab_pos : 0 < a * b := mul_pos ha hb
  have ha_rad_pos : 0 < a ^ 2 + 8 * b * c := by
    nlinarith [sq_pos_of_pos ha, mul_pos (show (0 : ℝ) < 8 by norm_num) hbc_pos]
  have hb_rad_pos : 0 < b ^ 2 + 8 * a * c := by
    nlinarith [sq_pos_of_pos hb, mul_pos (show (0 : ℝ) < 8 by norm_num) hac_pos]
  have hc_rad_pos : 0 < c ^ 2 + 8 * a * b := by
    nlinarith [sq_pos_of_pos hc, mul_pos (show (0 : ℝ) < 8 by norm_num) hab_pos]
  have ha_sqrt_pos : 0 < sqrt (a ^ 2 + 8 * b * c) := sqrt_pos_of_pos ha_rad_pos
  have hb_sqrt_pos : 0 < sqrt (b ^ 2 + 8 * a * c) := sqrt_pos_of_pos hb_rad_pos
  have hc_sqrt_pos : 0 < sqrt (c ^ 2 + 8 * a * b) := sqrt_pos_of_pos hc_rad_pos
  have ha_sqrt_ne : sqrt (a ^ 2 + 8 * b * c) ≠ 0 := ne_of_gt ha_sqrt_pos
  have hb_sqrt_ne : sqrt (b ^ 2 + 8 * a * c) ≠ 0 := ne_of_gt hb_sqrt_pos
  have hc_sqrt_ne : sqrt (c ^ 2 + 8 * a * b) ≠ 0 := ne_of_gt hc_sqrt_pos
  have ha_term_pos : 0 < a / sqrt (a ^ 2 + 8 * b * c) := div_pos ha ha_sqrt_pos
  have hb_term_pos : 0 < b / sqrt (b ^ 2 + 8 * a * c) := div_pos hb hb_sqrt_pos
  have hc_term_pos : 0 < c / sqrt (c ^ 2 + 8 * a * b) := div_pos hc hc_sqrt_pos
  have ha_sqrt_gt_num : a < sqrt (a ^ 2 + 8 * b * c) := by
    rw [Real.lt_sqrt (le_of_lt ha)]
    nlinarith [hbc_pos]
  have hb_sqrt_gt_num : b < sqrt (b ^ 2 + 8 * a * c) := by
    rw [Real.lt_sqrt (le_of_lt hb)]
    nlinarith [hac_pos]
  have hc_sqrt_gt_num : c < sqrt (c ^ 2 + 8 * a * b) := by
    rw [Real.lt_sqrt (le_of_lt hc)]
    nlinarith [hab_pos]
  have ha_term_lt_one : a / sqrt (a ^ 2 + 8 * b * c) < 1 :=
    (div_lt_one ha_sqrt_pos).2 ha_sqrt_gt_num
  have hb_term_lt_one : b / sqrt (b ^ 2 + 8 * a * c) < 1 :=
    (div_lt_one hb_sqrt_pos).2 hb_sqrt_gt_num
  have hc_term_lt_one : c / sqrt (c ^ 2 + 8 * a * b) < 1 :=
    (div_lt_one hc_sqrt_pos).2 hc_sqrt_gt_num
  have ha_sq :
      (a / sqrt (a ^ 2 + 8 * b * c)) ^ 2 =
        a ^ 2 / (a ^ 2 + 8 * b * c) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt ha_rad_pos)]
  have hb_sq :
      (b / sqrt (b ^ 2 + 8 * a * c)) ^ 2 =
        b ^ 2 / (b ^ 2 + 8 * a * c) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hb_rad_pos)]
  have hc_sq :
      (c / sqrt (c ^ 2 + 8 * a * b)) ^ 2 =
        c ^ 2 / (c ^ 2 + 8 * a * b) := by
    rw [div_pow, Real.sq_sqrt (le_of_lt hc_rad_pos)]
  have ha_sq_inv :
      (a / sqrt (a ^ 2 + 8 * b * c)) ^ 2 =
        1 / (1 + 8 * b * c / a ^ 2) := by
    rw [ha_sq]
    have ha2_ne : a ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt ha)
    have hden_ne : 1 + 8 * b * c / a ^ 2 ≠ 0 := by
      positivity
    field_simp [ha2_ne, hden_ne]
  have hb_sq_inv :
      (b / sqrt (b ^ 2 + 8 * a * c)) ^ 2 =
        1 / (1 + 8 * a * c / b ^ 2) := by
    rw [hb_sq]
    have hb2_ne : b ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hb)
    have hden_ne : 1 + 8 * a * c / b ^ 2 ≠ 0 := by
      positivity
    field_simp [hb2_ne, hden_ne]
  have hc_sq_inv :
      (c / sqrt (c ^ 2 + 8 * a * b)) ^ 2 =
        1 / (1 + 8 * a * b / c ^ 2) := by
    rw [hc_sq]
    have hc2_ne : c ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hc)
    have hden_ne : 1 + 8 * a * b / c ^ 2 ≠ 0 := by
      positivity
    field_simp [hc2_ne, hden_ne]
  have hscale_a_pos : 0 < 8 * b * c / a ^ 2 := by
    positivity
  have hscale_b_pos : 0 < 8 * a * c / b ^ 2 := by
    positivity
  have hscale_c_pos : 0 < 8 * a * b / c ^ 2 := by
    positivity
  have hscale_prod :
      (8 * b * c / a ^ 2) * (8 * a * c / b ^ 2) *
          (8 * a * b / c ^ 2) = 512 := by
    have ha_ne : a ≠ 0 := ne_of_gt ha
    have hb_ne : b ≠ 0 := ne_of_gt hb
    have hc_ne : c ≠ 0 := ne_of_gt hc
    field_simp [ha_ne, hb_ne, hc_ne]
    norm_num
  have ha_recip_sq_sub_one :
      1 / (a / sqrt (a ^ 2 + 8 * b * c)) ^ 2 - 1 =
        8 * b * c / a ^ 2 := by
    rw [ha_sq_inv]
    have hden_ne : 1 + 8 * b * c / a ^ 2 ≠ 0 := by
      positivity
    field_simp [hden_ne]
    ring
  have hb_recip_sq_sub_one :
      1 / (b / sqrt (b ^ 2 + 8 * a * c)) ^ 2 - 1 =
        8 * a * c / b ^ 2 := by
    rw [hb_sq_inv]
    have hden_ne : 1 + 8 * a * c / b ^ 2 ≠ 0 := by
      positivity
    field_simp [hden_ne]
    ring
  have hc_recip_sq_sub_one :
      1 / (c / sqrt (c ^ 2 + 8 * a * b)) ^ 2 - 1 =
        8 * a * b / c ^ 2 := by
    rw [hc_sq_inv]
    have hden_ne : 1 + 8 * a * b / c ^ 2 ≠ 0 := by
      positivity
    field_simp [hden_ne]
    ring
  have hterm_recip_sq_prod :
      (1 / (a / sqrt (a ^ 2 + 8 * b * c)) ^ 2 - 1) *
          (1 / (b / sqrt (b ^ 2 + 8 * a * c)) ^ 2 - 1) *
            (1 / (c / sqrt (c ^ 2 + 8 * a * b)) ^ 2 - 1) = 512 := by
    rw [ha_recip_sq_sub_one, hb_recip_sq_sub_one, hc_recip_sq_sub_one]
    exact hscale_prod
  have hcore :
      ∀ x y z : ℝ, 0 < x → x < 1 → 0 < y → y < 1 → 0 < z → z < 1 →
        (1 / x ^ 2 - 1) * (1 / y ^ 2 - 1) * (1 / z ^ 2 - 1) = 512 →
          x + y + z ≤ 2 := by
    intro x y z hx_pos hx_lt_one hy_pos hy_lt_one hz_pos hz_lt_one hprod
    by_contra hnot
    have hsum_gt : 2 < x + y + z := lt_of_not_ge hnot
    have hx_ne : x ≠ 0 := ne_of_gt hx_pos
    have hy_ne : y ≠ 0 := ne_of_gt hy_pos
    have hz_ne : z ≠ 0 := ne_of_gt hz_pos
    have hxyz_pos : 0 < x * y * z := by positivity
    have hden_pos : 0 < (x * y * z) ^ 2 := sq_pos_of_pos hxyz_pos
    have hx_def_pos : 0 < 1 - x := sub_pos.mpr hx_lt_one
    have hy_def_pos : 0 < 1 - y := sub_pos.mpr hy_lt_one
    have hz_def_pos : 0 < 1 - z := sub_pos.mpr hz_lt_one
    have hx_def_nonneg : 0 ≤ 1 - x := le_of_lt hx_def_pos
    have hy_def_nonneg : 0 ≤ 1 - y := le_of_lt hy_def_pos
    have hz_def_nonneg : 0 ≤ 1 - z := le_of_lt hz_def_pos
    have hx_def_le_yz : 1 - x ≤ y * z := by
      have hyz_gap_pos : 0 < (1 - y) * (1 - z) := mul_pos hy_def_pos hz_def_pos
      have hgap : 0 < x + y * z - 1 := by
        nlinarith only [hsum_gt, hyz_gap_pos]
      nlinarith only [hgap]
    have hy_def_le_xz : 1 - y ≤ x * z := by
      have hxz_gap_pos : 0 < (1 - x) * (1 - z) := mul_pos hx_def_pos hz_def_pos
      have hgap : 0 < y + x * z - 1 := by
        nlinarith only [hsum_gt, hxz_gap_pos]
      nlinarith only [hgap]
    have hz_def_le_xy : 1 - z ≤ x * y := by
      have hxy_gap_pos : 0 < (1 - x) * (1 - y) := mul_pos hx_def_pos hy_def_pos
      have hgap : 0 < z + x * y - 1 := by
        nlinarith only [hsum_gt, hxy_gap_pos]
      nlinarith only [hgap]
    have hdef_prod_nonneg : 0 ≤ (1 - x) * (1 - y) * (1 - z) := by positivity
    have hdef_prod_le :
        (1 - x) * (1 - y) * (1 - z) ≤ (x * y * z) ^ 2 := by
      have hyz_nonneg : 0 ≤ y * z := by positivity
      have hxz_nonneg : 0 ≤ x * z := by positivity
      have hxy_nonneg : 0 ≤ x * y := by positivity
      have hfirst :
          (1 - x) * (1 - y) ≤ (y * z) * (x * z) :=
        mul_le_mul hx_def_le_yz hy_def_le_xz hy_def_nonneg hyz_nonneg
      have hfirst_nonneg : 0 ≤ (1 - x) * (1 - y) := by positivity
      have hright_nonneg : 0 ≤ (y * z) * (x * z) := by positivity
      have hmul :
          (1 - x) * (1 - y) * (1 - z) ≤ (y * z) * (x * z) * (x * y) :=
        mul_le_mul hfirst hz_def_le_xy hz_def_nonneg hright_nonneg
      have hright_eq : (y * z) * (x * z) * (x * y) = (x * y * z) ^ 2 := by
        ring
      simpa [hright_eq] using hmul
    have hsum_factor_nonneg : 0 ≤ (1 + x) * (1 + y) * (1 + z) := by positivity
    have hsum_factor_lt :
        (1 + x) * (1 + y) * (1 + z) < 8 := by
      have hx_one_pos : 0 < 1 + x := by nlinarith only [hx_pos]
      have hy_one_pos : 0 < 1 + y := by nlinarith only [hy_pos]
      have hz_one_pos : 0 < 1 + z := by nlinarith only [hz_pos]
      have hx_two : 1 + x < 2 := by nlinarith only [hx_lt_one]
      have hy_two : 1 + y < 2 := by nlinarith only [hy_lt_one]
      have hz_two : 1 + z < 2 := by nlinarith only [hz_lt_one]
      have hxy_lt_four : (1 + x) * (1 + y) < 4 := by
        calc
          (1 + x) * (1 + y) < 2 * (1 + y) :=
            mul_lt_mul_of_pos_right hx_two hy_one_pos
          _ < 2 * 2 := mul_lt_mul_of_pos_left hy_two (by norm_num)
          _ = 4 := by norm_num
      have hlt1 : ((1 + x) * (1 + y)) * (1 + z) < 4 * (1 + z) := by
        exact mul_lt_mul_of_pos_right hxy_lt_four hz_one_pos
      have hlt2 : 4 * (1 + z) < 8 := by
        nlinarith only [hz_two]
      exact lt_trans hlt1 hlt2
    have hprod_rewrite :
        (1 / x ^ 2 - 1) * (1 / y ^ 2 - 1) * (1 / z ^ 2 - 1) =
          ((1 - x) * (1 - y) * (1 - z) * ((1 + x) * (1 + y) * (1 + z))) /
            ((x * y * z) ^ 2) := by
      field_simp [hx_ne, hy_ne, hz_ne]
      ring
    have hleft_div_le_one :
        ((1 - x) * (1 - y) * (1 - z)) / ((x * y * z) ^ 2) ≤ 1 :=
      (div_le_one hden_pos).2 hdef_prod_le
    have hprod_lt_eight :
        (1 / x ^ 2 - 1) * (1 / y ^ 2 - 1) * (1 / z ^ 2 - 1) < 8 := by
      rw [hprod_rewrite]
      calc
        ((1 - x) * (1 - y) * (1 - z) * ((1 + x) * (1 + y) * (1 + z))) /
            ((x * y * z) ^ 2)
            = (((1 - x) * (1 - y) * (1 - z)) / ((x * y * z) ^ 2)) *
                ((1 + x) * (1 + y) * (1 + z)) := by
                ring
        _ ≤ 1 * ((1 + x) * (1 + y) * (1 + z)) :=
            mul_le_mul_of_nonneg_right hleft_div_le_one hsum_factor_nonneg
        _ < 8 := by simpa using hsum_factor_lt
    nlinarith only [hprod, hprod_lt_eight]
  exact hcore
    (a / sqrt (a ^ 2 + 8 * b * c))
    (b / sqrt (b ^ 2 + 8 * a * c))
    (c / sqrt (c ^ 2 + 8 * a * b))
    ha_term_pos ha_term_lt_one hb_term_pos hb_term_lt_one hc_term_pos hc_term_lt_one
    hterm_recip_sq_prod
