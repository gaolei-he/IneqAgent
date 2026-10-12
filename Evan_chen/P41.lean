import Mathlib

theorem P41 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a + b + c) ^ 3 ≤ (a ^ 5 - a ^ 2 + 3) * (b ^ 5 - b ^ 2 + 3) * (c ^ 5 - c ^ 2 + 3) := by
  have hfactor_ge_two : ∀ x : ℝ, x > 0 → 2 ≤ x ^ 5 - x ^ 2 + 3 := by
    intro x hx
    by_cases hx1 : x ≤ 1
    · have hx0 : 0 ≤ x := le_of_lt hx
      have hx2_le_one : x ^ 2 ≤ 1 := (sq_le_one_iff₀ hx0).2 hx1
      have hx5_nonneg : 0 ≤ x ^ 5 := pow_nonneg hx0 5
      nlinarith
    · have hxge : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
      have hx2_le_x5 : x ^ 2 ≤ x ^ 5 := pow_le_pow_right₀ hxge (by norm_num : 2 ≤ 5)
      nlinarith
  have ha_factor_ge_two : 2 ≤ a ^ 5 - a ^ 2 + 3 := hfactor_ge_two a ha
  have hb_factor_ge_two : 2 ≤ b ^ 5 - b ^ 2 + 3 := hfactor_ge_two b hb
  have hc_factor_ge_two : 2 ≤ c ^ 5 - c ^ 2 + 3 := hfactor_ge_two c hc
  have ha_factor_nonneg : 0 ≤ a ^ 5 - a ^ 2 + 3 := by nlinarith
  have hb_factor_nonneg : 0 ≤ b ^ 5 - b ^ 2 + 3 := by nlinarith
  have hc_factor_nonneg : 0 ≤ c ^ 5 - c ^ 2 + 3 := by nlinarith
  have hfactor_ge_three_mul : ∀ x : ℝ, x > 0 → 3 * x ≤ x ^ 5 - x ^ 2 + 3 := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hsq_nonneg : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
    have htail_nonneg : 0 ≤ x ^ 3 + 2 * x ^ 2 + 3 * x + 3 := by
      have hx2_nonneg : 0 ≤ x ^ 2 := pow_nonneg hx0 2
      have hx3_nonneg : 0 ≤ x ^ 3 := pow_nonneg hx0 3
      nlinarith
    have hprod_nonneg :
        0 ≤ (x - 1) ^ 2 * (x ^ 3 + 2 * x ^ 2 + 3 * x + 3) :=
      mul_nonneg hsq_nonneg htail_nonneg
    have hfactor_identity :
        x ^ 5 - x ^ 2 + 3 - 3 * x =
          (x - 1) ^ 2 * (x ^ 3 + 2 * x ^ 2 + 3 * x + 3) := by
      ring
    nlinarith
  have ha_factor_ge_three_mul : 3 * a ≤ a ^ 5 - a ^ 2 + 3 :=
    hfactor_ge_three_mul a ha
  have hb_factor_ge_three_mul : 3 * b ≤ b ^ 5 - b ^ 2 + 3 :=
    hfactor_ge_three_mul b hb
  have hc_factor_ge_three_mul : 3 * c ≤ c ^ 5 - c ^ 2 + 3 :=
    hfactor_ge_three_mul c hc
  have hfactor_ge_cube_plus_two : ∀ x : ℝ, x > 0 → x ^ 3 + 2 ≤ x ^ 5 - x ^ 2 + 3 := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt hx
    have hsq_nonneg : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
    have hx_plus_one_nonneg : 0 ≤ x + 1 := by nlinarith
    have hquad_nonneg : 0 ≤ x ^ 2 + x + 1 := by
      have hx2_nonneg : 0 ≤ x ^ 2 := pow_nonneg hx0 2
      nlinarith
    have hprod_nonneg : 0 ≤ (x - 1) ^ 2 * (x + 1) * (x ^ 2 + x + 1) := by
      exact mul_nonneg (mul_nonneg hsq_nonneg hx_plus_one_nonneg) hquad_nonneg
    have hfactor_identity :
        x ^ 5 - x ^ 2 + 3 - (x ^ 3 + 2) =
          (x - 1) ^ 2 * (x + 1) * (x ^ 2 + x + 1) := by
      ring
    nlinarith
  have ha_factor_ge_cube_plus_two : a ^ 3 + 2 ≤ a ^ 5 - a ^ 2 + 3 :=
    hfactor_ge_cube_plus_two a ha
  have hb_factor_ge_cube_plus_two : b ^ 3 + 2 ≤ b ^ 5 - b ^ 2 + 3 :=
    hfactor_ge_cube_plus_two b hb
  have hc_factor_ge_cube_plus_two : c ^ 3 + 2 ≤ c ^ 5 - c ^ 2 + 3 :=
    hfactor_ge_cube_plus_two c hc
  have ha_cube_plus_two_nonneg : 0 ≤ a ^ 3 + 2 := by
    have ha0 : 0 ≤ a := le_of_lt ha
    have ha3_nonneg : 0 ≤ a ^ 3 := pow_nonneg ha0 3
    nlinarith
  have hb_cube_plus_two_nonneg : 0 ≤ b ^ 3 + 2 := by
    have hb0 : 0 ≤ b := le_of_lt hb
    have hb3_nonneg : 0 ≤ b ^ 3 := pow_nonneg hb0 3
    nlinarith
  have hc_cube_plus_two_nonneg : 0 ≤ c ^ 3 + 2 := by
    have hc0 : 0 ≤ c := le_of_lt hc
    have hc3_nonneg : 0 ≤ c ^ 3 := pow_nonneg hc0 3
    nlinarith
  have hcube_plus_two_product_le_prod :
      (a ^ 3 + 2) * (b ^ 3 + 2) * (c ^ 3 + 2) ≤
        (a ^ 5 - a ^ 2 + 3) * (b ^ 5 - b ^ 2 + 3) * (c ^ 5 - c ^ 2 + 3) := by
    have hAB_ge :
        (a ^ 3 + 2) * (b ^ 3 + 2) ≤
          (a ^ 5 - a ^ 2 + 3) * (b ^ 5 - b ^ 2 + 3) := by
      exact mul_le_mul ha_factor_ge_cube_plus_two hb_factor_ge_cube_plus_two
        hb_cube_plus_two_nonneg ha_factor_nonneg
    have hAB_nonneg : 0 ≤ (a ^ 3 + 2) * (b ^ 3 + 2) :=
      mul_nonneg ha_cube_plus_two_nonneg hb_cube_plus_two_nonneg
    exact mul_le_mul hAB_ge hc_factor_ge_cube_plus_two hc_cube_plus_two_nonneg
      (mul_nonneg ha_factor_nonneg hb_factor_nonneg)
  have hholder_cube :
      (a + b + c) ^ 3 ≤ (a ^ 3 + 2) * (b ^ 3 + 2) * (c ^ 3 + 2) := by
    let A : ℝ := a ^ 3 + 2
    let B : ℝ := b ^ 3 + 2
    let C : ℝ := c ^ 3 + 2
    have hA_nonneg : 0 ≤ A := by
      dsimp [A]
      have ha3_nonneg : 0 ≤ a ^ 3 := pow_nonneg (le_of_lt ha) 3
      nlinarith
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      have hb3_nonneg : 0 ≤ b ^ 3 := pow_nonneg (le_of_lt hb) 3
      nlinarith
    have hC_nonneg : 0 ≤ C := by
      dsimp [C]
      have hc3_nonneg : 0 ≤ c ^ 3 := pow_nonneg (le_of_lt hc) 3
      nlinarith
    have hpq : Real.HolderConjugate (3 : ℝ) (3 / 2 : ℝ) := by
      rw [Real.holderConjugate_iff]
      norm_num
    have hfirst :
        a + b + c ≤
          A ^ ((1 : ℝ) / 3) *
            (1 + b ^ ((3 : ℝ) / 2) + c ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3) := by
      have h := Real.inner_le_Lp_mul_Lq_of_nonneg
        (s := (Finset.univ : Finset (Fin 3)))
        (f := fun i : Fin 3 => ![a, (1 : ℝ), (1 : ℝ)] i)
        (g := fun i : Fin 3 => ![(1 : ℝ), b, c] i)
        hpq
        (by intro i hi; fin_cases i <;> simp [le_of_lt ha])
        (by intro i hi; fin_cases i <;> simp [le_of_lt hb, le_of_lt hc])
      convert h using 2 <;> (simp [A, Fin.sum_univ_three]; try ring_nf)
    have hpqr : Real.HolderTriple (3 : ℝ) 3 (3 / 2 : ℝ) := by
      rw [Real.holderTriple_iff]
      norm_num
    have hsecond :
        1 + b ^ ((3 : ℝ) / 2) + c ^ ((3 : ℝ) / 2) ≤
          B ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
      have h := Real.Lr_rpow_le_Lp_mul_Lq_of_nonneg
        (s := (Finset.univ : Finset (Fin 3)))
        (f := fun i : Fin 3 => ![(1 : ℝ), b, (1 : ℝ)] i)
        (g := fun i : Fin 3 => ![(1 : ℝ), (1 : ℝ), c] i)
        hpqr
        (by intro i hi; fin_cases i <;> simp [le_of_lt hb])
        (by intro i hi; fin_cases i <;> simp [le_of_lt hc])
      convert h using 2 <;> (simp [B, C, Fin.sum_univ_three]; try ring_nf)
    have hmiddle_nonneg : 0 ≤ 1 + b ^ ((3 : ℝ) / 2) + c ^ ((3 : ℝ) / 2) := by
      positivity
    have hsecond_pow :=
      Real.rpow_le_rpow hmiddle_nonneg hsecond (by norm_num : 0 ≤ (2 : ℝ) / 3)
    have hlinear :
        a + b + c ≤
          A ^ ((1 : ℝ) / 3) *
            (B ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) ^ ((2 : ℝ) / 3) := by
      exact hfirst.trans (mul_le_mul_of_nonneg_left hsecond_pow (by positivity))
    have hsum_nonneg : 0 ≤ a + b + c := by nlinarith
    have hpow := pow_le_pow_left₀ hsum_nonneg hlinear 3
    have hrhs_cube :
        (A ^ ((1 : ℝ) / 3) *
            (B ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2)) ^ ((2 : ℝ) / 3)) ^ 3 =
          A * B * C := by
      have hBC : 0 ≤ B ^ ((1 : ℝ) / 2) * C ^ ((1 : ℝ) / 2) := by
        positivity
      rw [mul_pow]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hA_nonneg]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hBC]
      norm_num
      conv_lhs => rw [mul_pow]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hB_nonneg]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hC_nonneg]
      norm_num
      ring
    dsimp [A, B, C] at hrhs_cube hpow ⊢
    rwa [hrhs_cube] at hpow
  exact hholder_cube.trans hcube_plus_two_product_le_prod
