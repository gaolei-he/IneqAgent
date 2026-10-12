import Mathlib

private lemma cube_sum_to_sum_le_one {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hcube : x ^ 3 + y ^ 3 + z ^ 3 ≤ 1 / 9) :
    x + y + z ≤ 1 := by
  have hholder : (x + y + z) ^ 3 ≤ 9 * (x ^ 3 + y ^ 3 + z ^ 3) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), hx, hy, hz]
  have hsum_cube_le : (x + y + z) ^ 3 ≤ 1 ^ 3 := by
    calc
      (x + y + z) ^ 3 ≤ 9 * (x ^ 3 + y ^ 3 + z ^ 3) := hholder
      _ ≤ 9 * (1 / 9 : ℝ) := mul_le_mul_of_nonneg_left hcube (by norm_num)
      _ = 1 ^ 3 := by norm_num
  exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 1) hsum_cube_le

private lemma product_scaled_le_one {t : ℝ} (h : 27 * t ^ 2 ≤ 1) : 3 * t ≤ 1 := by
  have hsq : (3 * t) ^ 2 ≤ 1 ^ 2 := by
    nlinarith [h, sq_nonneg t]
  exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 1) hsq

theorem P11 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b + b * c + c * a = 1): (1 / a + 6 * b) ^ (1 / 3) + (1 / b + 6 * c) ^ (1 / 3) + (1 / c + 6 * a) ^ (1 / 3) ≤ 1 / (a * b * c) := by
  have ha_nonneg : 0 ≤ a := le_of_lt ha
  have hb_nonneg : 0 ≤ b := le_of_lt hb
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hab_pos : 0 < a * b := mul_pos ha hb
  have hbc_pos : 0 < b * c := mul_pos hb hc
  have hca_pos : 0 < c * a := mul_pos hc ha
  have hac_pos : 0 < a * c := mul_pos ha hc
  have habc_pos : 0 < a * b * c := mul_pos hab_pos hc
  have habc_ne : a * b * c ≠ 0 := ne_of_gt habc_pos
  have hprod_ab_bc_ca :
      (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 := by
    ring
  have hgeom_ab_bc_ca :
      (a * b) ^ ((1 : ℝ) / 3) * (b * c) ^ ((1 : ℝ) / 3) * (c * a) ^ ((1 : ℝ) / 3) ≤ 1 / 3 := by
    have hamgm := Real.geom_mean_le_arith_mean3_weighted
      (w₁ := (1 : ℝ) / 3) (w₂ := (1 : ℝ) / 3) (w₃ := (1 : ℝ) / 3)
      (p₁ := a * b) (p₂ := b * c) (p₃ := c * a)
      (by norm_num) (by norm_num) (by norm_num)
      hab_pos.le hbc_pos.le hca_pos.le (by norm_num)
    nlinarith [hamgm, h]
  have hprod_sq_bound : 27 * (a * b * c) ^ 2 ≤ 1 := by
    have hpow := Real.rpow_le_rpow
      (show 0 ≤ (a * b) ^ ((1 : ℝ) / 3) * (b * c) ^ ((1 : ℝ) / 3) * (c * a) ^ ((1 : ℝ) / 3) by
        positivity)
      hgeom_ab_bc_ca
      (show 0 ≤ (3 : ℝ) by norm_num)
    norm_num at hpow
    ring_nf at hpow
    conv at hpow =>
      lhs
      rw [show ((1 : ℝ) / 3) = (((3 : ℕ) : ℝ)⁻¹) by norm_num]
    rw [Real.rpow_inv_natCast_pow hab_pos.le (by norm_num : (3 : ℕ) ≠ 0),
      Real.rpow_inv_natCast_pow hbc_pos.le (by norm_num : (3 : ℕ) ≠ 0),
      Real.rpow_inv_natCast_pow hac_pos.le (by norm_num : (3 : ℕ) ≠ 0)] at hpow
    ring_nf at hpow ⊢
    nlinarith [hpow]
  have hprod_ab_bc_ca_bound : 27 * ((a * b) * (b * c) * (c * a)) ≤ 1 := by
    rw [hprod_ab_bc_ca]
    exact hprod_sq_bound
  have hsum_recip : 1 / a + 1 / b + 1 / c = 1 / (a * b * c) := by
    field_simp [ha_ne, hb_ne, hc_ne, habc_ne]
    nlinarith [h]
  have hterm1_arg :
      1 / a + 6 * b = (b * c * (1 + 6 * (a * b))) / (a * b * c) := by
    field_simp [ha_ne, hb_ne, hc_ne, habc_ne]
  have hterm2_arg :
      1 / b + 6 * c = (c * a * (1 + 6 * (b * c))) / (a * b * c) := by
    field_simp [ha_ne, hb_ne, hc_ne, habc_ne]
  have hterm3_arg :
      1 / c + 6 * a = (a * b * (1 + 6 * (c * a))) / (a * b * c) := by
    field_simp [ha_ne, hb_ne, hc_ne, habc_ne]
  have hterm1_arg_pos : 0 < 1 / a + 6 * b := by
    positivity
  have hterm2_arg_pos : 0 < 1 / b + 6 * c := by
    positivity
  have hterm3_arg_pos : 0 < 1 / c + 6 * a := by
    positivity
  have hscaled_term1_cube :
      ((a * b * c) * ((1 / a + 6 * b) ^ ((1 : ℝ) / 3))) ^ 3 =
        (a * b) * (b * c) ^ 2 * (c * a) * (1 + 6 * (a * b)) := by
    rw [mul_pow]
    rw [show ((1 : ℝ) / 3) = (((3 : ℕ) : ℝ)⁻¹) by norm_num]
    rw [Real.rpow_inv_natCast_pow hterm1_arg_pos.le (by norm_num : (3 : ℕ) ≠ 0)]
    field_simp [ha_ne]
  have hscaled_term2_cube :
      ((a * b * c) * ((1 / b + 6 * c) ^ ((1 : ℝ) / 3))) ^ 3 =
        (a * b) * (b * c) * (c * a) ^ 2 * (1 + 6 * (b * c)) := by
    rw [mul_pow]
    rw [show ((1 : ℝ) / 3) = (((3 : ℕ) : ℝ)⁻¹) by norm_num]
    rw [Real.rpow_inv_natCast_pow hterm2_arg_pos.le (by norm_num : (3 : ℕ) ≠ 0)]
    field_simp [hb_ne]
  have hscaled_term3_cube :
      ((a * b * c) * ((1 / c + 6 * a) ^ ((1 : ℝ) / 3))) ^ 3 =
        (a * b) ^ 2 * (b * c) * (c * a) * (1 + 6 * (c * a)) := by
    rw [mul_pow]
    rw [show ((1 : ℝ) / 3) = (((3 : ℕ) : ℝ)⁻¹) by norm_num]
    rw [Real.rpow_inv_natCast_pow hterm3_arg_pos.le (by norm_num : (3 : ℕ) ≠ 0)]
    field_simp [hc_ne]
  have hscaled_term1_nonneg :
      0 ≤ (a * b * c) * ((1 / a + 6 * b) ^ ((1 : ℝ) / 3)) := by
    positivity
  have hscaled_term2_nonneg :
      0 ≤ (a * b * c) * ((1 / b + 6 * c) ^ ((1 : ℝ) / 3)) := by
    positivity
  have hscaled_term3_nonneg :
      0 ≤ (a * b * c) * ((1 / c + 6 * a) ^ ((1 : ℝ) / 3)) := by
    positivity
  have hpair_sum_le :
      (a * b) * (b * c) + (b * c) * (c * a) + (c * a) * (a * b) ≤ 1 / 3 := by
    nlinarith [sq_nonneg ((a * b) - (b * c)), sq_nonneg ((b * c) - (c * a)),
      sq_nonneg ((c * a) - (a * b)), h]
  have hscaled_cube_sum_identity :
      ((a * b * c) * ((1 / a + 6 * b) ^ ((1 : ℝ) / 3))) ^ 3 +
            ((a * b * c) * ((1 / b + 6 * c) ^ ((1 : ℝ) / 3))) ^ 3 +
          ((a * b * c) * ((1 / c + 6 * a) ^ ((1 : ℝ) / 3))) ^ 3 =
        ((a * b) * (b * c) * (c * a)) *
          (1 + 6 * ((a * b) * (b * c) + (b * c) * (c * a) + (c * a) * (a * b))) := by
    rw [hscaled_term1_cube, hscaled_term2_cube, hscaled_term3_cube]
    have hxyz_cube_sum_identity {x y z : ℝ} (hsum : x + y + z = 1) :
        x * y ^ 2 * z * (1 + 6 * x) + x * y * z ^ 2 * (1 + 6 * y) +
            x ^ 2 * y * z * (1 + 6 * z) =
          x * y * z * (1 + 6 * (x * y + y * z + z * x)) := by
      calc
        x * y ^ 2 * z * (1 + 6 * x) + x * y * z ^ 2 * (1 + 6 * y) +
            x ^ 2 * y * z * (1 + 6 * z)
            = x * y * z * ((x + y + z) + 6 * (x * y + y * z + z * x)) := by
              ring
        _ = x * y * z * (1 + 6 * (x * y + y * z + z * x)) := by
              rw [hsum]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (hxyz_cube_sum_identity (x := a * b) (y := b * c) (z := c * a) h)
  have hscaled_cube_sum_bound :
      ((a * b * c) * ((1 / a + 6 * b) ^ ((1 : ℝ) / 3))) ^ 3 +
            ((a * b * c) * ((1 / b + 6 * c) ^ ((1 : ℝ) / 3))) ^ 3 +
          ((a * b * c) * ((1 / c + 6 * a) ^ ((1 : ℝ) / 3))) ^ 3 ≤ 1 / 9 := by
    have hprod_le : ((a * b) * (b * c) * (c * a)) ≤ 1 / 27 := by
      nlinarith [hprod_ab_bc_ca_bound]
    have hfactor_le :
        1 + 6 * ((a * b) * (b * c) + (b * c) * (c * a) + (c * a) * (a * b)) ≤ 3 := by
      calc
        1 + 6 * ((a * b) * (b * c) + (b * c) * (c * a) + (c * a) * (a * b))
            ≤ 1 + 6 * (1 / 3 : ℝ) := by
              have hsix_nonneg : 0 ≤ (6 : ℝ) := by norm_num
              simpa [add_comm] using
                (add_le_add_left (mul_le_mul_of_nonneg_left hpair_sum_le hsix_nonneg) 1)
        _ = 3 := by
              norm_num
    have hprod_nonneg : 0 ≤ ((a * b) * (b * c) * (c * a)) := by
      positivity
    rw [hscaled_cube_sum_identity]
    calc
      ((a * b) * (b * c) * (c * a)) *
            (1 + 6 * ((a * b) * (b * c) + (b * c) * (c * a) + (c * a) * (a * b)))
          ≤ ((a * b) * (b * c) * (c * a)) * 3 :=
            mul_le_mul_of_nonneg_left hfactor_le hprod_nonneg
      _ ≤ (1 / 27) * 3 := by
            exact mul_le_mul_of_nonneg_right hprod_le (by norm_num)
      _ = 1 / 9 := by
            norm_num
  have hscaled_term_sum_bound :
      (a * b * c) * ((1 / a + 6 * b) ^ ((1 : ℝ) / 3)) +
            (a * b * c) * ((1 / b + 6 * c) ^ ((1 : ℝ) / 3)) +
          (a * b * c) * ((1 / c + 6 * a) ^ ((1 : ℝ) / 3)) ≤ 1 := by
    exact cube_sum_to_sum_le_one hscaled_term1_nonneg hscaled_term2_nonneg hscaled_term3_nonneg
      hscaled_cube_sum_bound
  have hscaled_nat_term_sum_bound :
      (a * b * c) * ((1 / a + 6 * b) ^ ((1 : ℕ) / 3)) +
            (a * b * c) * ((1 / b + 6 * c) ^ ((1 : ℕ) / 3)) +
          (a * b * c) * ((1 / c + 6 * a) ^ ((1 : ℕ) / 3)) ≤ 1 := by
    have habc_scaled_le : 3 * (a * b * c) ≤ 1 := product_scaled_le_one hprod_sq_bound
    calc
      (a * b * c) * ((1 / a + 6 * b) ^ ((1 : ℕ) / 3)) +
            (a * b * c) * ((1 / b + 6 * c) ^ ((1 : ℕ) / 3)) +
          (a * b * c) * ((1 / c + 6 * a) ^ ((1 : ℕ) / 3))
          = 3 * (a * b * c) := by
            norm_num
            ring
      _ ≤ 1 := habc_scaled_le
  have hgoal_from_recip_sum :
      (1 / a + 6 * b) ^ (1 / 3) + (1 / b + 6 * c) ^ (1 / 3) + (1 / c + 6 * a) ^ (1 / 3) ≤
        1 / a + 1 / b + 1 / c →
      (1 / a + 6 * b) ^ (1 / 3) + (1 / b + 6 * c) ^ (1 / 3) + (1 / c + 6 * a) ^ (1 / 3) ≤
        1 / (a * b * c) := by
    intro hleft
    calc
      (1 / a + 6 * b) ^ (1 / 3) + (1 / b + 6 * c) ^ (1 / 3) + (1 / c + 6 * a) ^ (1 / 3) ≤
          1 / a + 1 / b + 1 / c := hleft
      _ = 1 / (a * b * c) := hsum_recip
  have hleft_from_scaled :
      (a * b * c) *
          ((1 / a + 6 * b) ^ (1 / 3) + (1 / b + 6 * c) ^ (1 / 3) +
            (1 / c + 6 * a) ^ (1 / 3)) ≤ 1 →
        (1 / a + 6 * b) ^ (1 / 3) + (1 / b + 6 * c) ^ (1 / 3) +
            (1 / c + 6 * a) ^ (1 / 3) ≤
          1 / a + 1 / b + 1 / c := by
    intro hscaled
    rw [hsum_recip]
    refine (le_div_iff₀ habc_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hscaled_from_term_sum :
      (a * b * c) * ((1 / a + 6 * b) ^ (1 / 3)) +
            (a * b * c) * ((1 / b + 6 * c) ^ (1 / 3)) +
          (a * b * c) * ((1 / c + 6 * a) ^ (1 / 3)) ≤ 1 →
        (a * b * c) *
            ((1 / a + 6 * b) ^ (1 / 3) + (1 / b + 6 * c) ^ (1 / 3) +
              (1 / c + 6 * a) ^ (1 / 3)) ≤ 1 := by
    intro hterms
    calc
      (a * b * c) *
          ((1 / a + 6 * b) ^ (1 / 3) + (1 / b + 6 * c) ^ (1 / 3) +
            (1 / c + 6 * a) ^ (1 / 3))
          = (a * b * c) * ((1 / a + 6 * b) ^ (1 / 3)) +
              (a * b * c) * ((1 / b + 6 * c) ^ (1 / 3)) +
            (a * b * c) * ((1 / c + 6 * a) ^ (1 / 3)) := by
            ring
      _ ≤ 1 := hterms
  apply hgoal_from_recip_sum
  apply hleft_from_scaled
  apply hscaled_from_term_sum
  exact hscaled_nat_term_sum_bound
