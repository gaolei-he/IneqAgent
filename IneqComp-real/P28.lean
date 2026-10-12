import Mathlib

theorem real_p28 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = a * b * c) : a^7 *(b * c - 1) + b^7 *(c * a - 1) + c^7 *(a * b - 1) ≥ 162 * √3 := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have habc_pos : 0 < a * b * c := by positivity
  have hbc_sub : b * c - 1 = (b + c) / a := by
    have hmul : a * (b * c - 1) = b + c := by nlinarith
    field_simp [ha_ne, hmul]
    nlinarith
  have hca_sub : c * a - 1 = (c + a) / b := by
    have hmul : b * (c * a - 1) = c + a := by nlinarith
    field_simp [hb_ne, hmul]
    nlinarith
  have hab_sub : a * b - 1 = (a + b) / c := by
    have hmul : c * (a * b - 1) = a + b := by nlinarith
    field_simp [hc_ne, hmul]
    nlinarith
  have term_a : a^7 * (b * c - 1) = a^6 * (b + c) := by
    rw [hbc_sub]
    field_simp [ha_ne]
  have term_b : b^7 * (c * a - 1) = b^6 * (c + a) := by
    rw [hca_sub]
    field_simp [hb_ne]
  have term_c : c^7 * (a * b - 1) = c^6 * (a + b) := by
    rw [hab_sub]
    field_simp [hc_ne]
  have lhs_eq :
      a^7 *(b * c - 1) + b^7 *(c * a - 1) + c^7 *(a * b - 1)
        = a^6 * (b + c) + b^6 * (c + a) + c^6 * (a + b) := by
    rw [term_a, term_b, term_c]
  have lhs_expanded :
      a^6 * (b + c) + b^6 * (c + a) + c^6 * (a + b)
        = a^6 * b + a^6 * c + b^6 * c + b^6 * a + c^6 * a + c^6 * b := by
    ring
  have lhs_eq_six :
      a^7 *(b * c - 1) + b^7 *(c * a - 1) + c^7 *(a * b - 1)
        = a^6 * b + a^6 * c + b^6 * c + b^6 * a + c^6 * a + c^6 * b := by
    rw [lhs_eq, lhs_expanded]
  have mon_pos_a_b : 0 < a^6 * b := by positivity
  have mon_pos_a_c : 0 < a^6 * c := by positivity
  have mon_pos_b_c : 0 < b^6 * c := by positivity
  have mon_pos_b_a : 0 < b^6 * a := by positivity
  have mon_pos_c_a : 0 < c^6 * a := by positivity
  have mon_pos_c_b : 0 < c^6 * b := by positivity
  have mon_prod :
      (a^6 * b) * (a^6 * c) * (b^6 * c) * (b^6 * a) * (c^6 * a) * (c^6 * b)
        = (a * b * c)^14 := by
    ring
  have amgm_six_terms :
      6 * (((a^6 * b) * (a^6 * c) * (b^6 * c) * (b^6 * a) * (c^6 * a) * (c^6 * b)) ^ ((1 : ℝ) / 6))
        ≤ a^6 * b + a^6 * c + b^6 * c + b^6 * a + c^6 * a + c^6 * b := by
    let z : Fin 6 → ℝ := ![
      a^6 * b,
      a^6 * c,
      b^6 * c,
      b^6 * a,
      c^6 * a,
      c^6 * b]
    have hz : ∀ i ∈ (Finset.univ : Finset (Fin 6)), 0 ≤ z i := by
      intro i hi
      fin_cases i <;> simp [z, le_of_lt mon_pos_a_b, le_of_lt mon_pos_a_c,
        le_of_lt mon_pos_b_c, le_of_lt mon_pos_b_a, le_of_lt mon_pos_c_a,
        le_of_lt mon_pos_c_b]
    have hgeom :=
      Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin 6)) (fun _ : Fin 6 => (1 : ℝ)) z
        (by intro i hi; norm_num)
        (by norm_num)
        hz
    have hgeom' :
        ((∏ i : Fin 6, z i) ^ ((1 : ℝ) / 6)) ≤ (∑ i : Fin 6, z i) / 6 := by
      simpa [div_eq_mul_inv] using hgeom
    have hgeom_mul : 6 * ((∏ i : Fin 6, z i) ^ ((1 : ℝ) / 6)) ≤ ∑ i : Fin 6, z i := by
      nlinarith
    have hprod_z :
        (∏ i : Fin 6, z i)
          = (a^6 * b) * (a^6 * c) * (b^6 * c) * (b^6 * a) * (c^6 * a) * (c^6 * b) := by
      simp [z, Fin.prod_univ_succ]
      ring
    have hsum_z :
        (∑ i : Fin 6, z i)
          = a^6 * b + a^6 * c + b^6 * c + b^6 * a + c^6 * a + c^6 * b := by
      simp [z, Fin.sum_univ_succ]
      ring
    simpa [hprod_z, hsum_z]
      using hgeom_mul
  have sum_cube_ge : 27 * (a * b * c) ≤ (a + b + c)^3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a + b - 2 * c), sq_nonneg (b + c - 2 * a),
      sq_nonneg (c + a - 2 * b)]
  have habc_cubic_ge : 27 * (a * b * c) ≤ (a * b * c)^3 := by
    simpa [h] using sum_cube_ge
  have habc_sq_ge : 27 ≤ (a * b * c)^2 := by
    nlinarith
  have habc_lower : 3 * √3 ≤ a * b * c := by
    have hconst_sq : (3 * √3) ^ 2 = 27 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have hconst_nonneg : 0 ≤ 3 * √3 := by positivity
    exact (sq_le_sq₀ hconst_nonneg (le_of_lt habc_pos)).mp (by simpa [hconst_sq] using habc_sq_ge)
  have amgm_abc :
      6 * (((a * b * c)^14) ^ ((1 : ℝ) / 6))
        ≤ a^6 * b + a^6 * c + b^6 * c + b^6 * a + c^6 * a + c^6 * b := by
    simpa [mon_prod] using amgm_six_terms
  have habc_rpow_norm :
      (((a * b * c)^14) ^ (6 : ℝ)⁻¹) = (a * b * c) ^ ((7 : ℝ) / 3) := by
    rw [← Real.rpow_natCast (a * b * c) 14]
    rw [← Real.rpow_mul (le_of_lt habc_pos)]
    norm_num
  have amgm_abc_rpow :
      6 * ((a * b * c) ^ ((7 : ℝ) / 3))
        ≤ a^6 * b + a^6 * c + b^6 * c + b^6 * a + c^6 * a + c^6 * b := by
    simpa [habc_rpow_norm] using amgm_abc
  have rpow_lower :
      (3 * √3 : ℝ) ^ ((7 : ℝ) / 3) ≤ (a * b * c) ^ ((7 : ℝ) / 3) := by
    exact Real.rpow_le_rpow (by positivity) habc_lower (by norm_num)
  have target_const :
      6 * ((3 * √3 : ℝ) ^ ((7 : ℝ) / 3)) = 162 * √3 := by
    have hbase : (3 * √3 : ℝ) = 3 ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + (1 / 2 : ℝ) by norm_num]
      rw [Real.rpow_add (by positivity)]
      rw [Real.sqrt_eq_rpow]
      norm_num
    rw [hbase]
    have hpow : ((3 : ℝ) ^ (3 / 2 : ℝ)) ^ ((7 : ℝ) / 3) = 3 ^ ((7 : ℝ) / 2) := by
      rw [← Real.rpow_mul (by positivity)]
      norm_num
    rw [hpow]
    have hsplit : (7 : ℝ) / 2 = 3 + 1 / 2 := by norm_num
    rw [hsplit, Real.rpow_add (by positivity)]
    rw [Real.sqrt_eq_rpow]
    ring
  have scaled_lower : 162 * √3 ≤ 6 * ((a * b * c) ^ ((7 : ℝ) / 3)) := by
    rw [← target_const]
    nlinarith
  have six_terms_lower :
      162 * √3 ≤ a^6 * b + a^6 * c + b^6 * c + b^6 * a + c^6 * a + c^6 * b :=
    le_trans scaled_lower amgm_abc_rpow
  rw [lhs_eq_six]
  exact six_terms_lower
