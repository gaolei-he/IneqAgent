import Mathlib

theorem P20 {a b c d : ℝ} (ha : a - b ≥ 0) (hb : b - c ≥ 0) (hc : c - d ≥ 0) (hd : d > 0) (h : a + b + c + d = 1) : (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d ≤ 1 := by
  have hab_order : a ≥ b := by linarith
  have hbc_order : b ≥ c := by linarith
  have hcd_order : c ≥ d := by linarith
  have hd_nonneg : d ≥ 0 := le_of_lt hd
  have hc_pos : c > 0 := by linarith
  have hb_pos : b > 0 := by linarith
  have ha_pos : a > 0 := by linarith
  have hc_nonneg : c ≥ 0 := le_of_lt hc_pos
  have hb_nonneg : b ≥ 0 := le_of_lt hb_pos
  have ha_nonneg : a ≥ 0 := le_of_lt ha_pos
  have ha_lt_one : a < 1 := by linarith
  have hb_lt_one : b < 1 := by linarith
  have hc_lt_one : c < 1 := by linarith
  have hd_lt_one : d < 1 := by linarith
  have ha_rpow_pos : 0 < a ^ a := Real.rpow_pos_of_pos ha_pos a
  have hb_rpow_pos : 0 < b ^ b := Real.rpow_pos_of_pos hb_pos b
  have hc_rpow_pos : 0 < c ^ c := Real.rpow_pos_of_pos hc_pos c
  have hd_rpow_pos : 0 < d ^ d := Real.rpow_pos_of_pos hd d
  have ha_rpow_le_one : a ^ a ≤ 1 := by
    exact Real.rpow_le_one ha_nonneg (le_of_lt ha_lt_one) (le_of_lt ha_pos)
  have hb_rpow_le_one : b ^ b ≤ 1 := by
    exact Real.rpow_le_one hb_nonneg (le_of_lt hb_lt_one) (le_of_lt hb_pos)
  have hc_rpow_le_one : c ^ c ≤ 1 := by
    exact Real.rpow_le_one hc_nonneg (le_of_lt hc_lt_one) (le_of_lt hc_pos)
  have hd_rpow_le_one : d ^ d ≤ 1 := by
    exact Real.rpow_le_one hd_nonneg (le_of_lt hd_lt_one) (le_of_lt hd)
  have hprod_pos : 0 < a ^ a * b ^ b * c ^ c * d ^ d := by positivity
  have hprod_le_one : a ^ a * b ^ b * c ^ c * d ^ d ≤ 1 := by
    have hab_rpow_le_one : a ^ a * b ^ b ≤ 1 := by
      exact mul_le_one₀ ha_rpow_le_one (le_of_lt hb_rpow_pos) hb_rpow_le_one
    have habc_rpow_le_one : a ^ a * b ^ b * c ^ c ≤ 1 := by
      exact mul_le_one₀ hab_rpow_le_one (le_of_lt hc_rpow_pos) hc_rpow_le_one
    exact mul_le_one₀ habc_rpow_le_one (le_of_lt hd_rpow_pos) hd_rpow_le_one
  have h_weight_pos : a + 2 * b + 3 * c + 4 * d > 0 := by positivity
  have h_weight_eq : a + 2 * b + 3 * c + 4 * d = 1 + b + 2 * c + 3 * d := by
    linarith
  have h_weight_le_five_halves : a + 2 * b + 3 * c + 4 * d ≤ (5 : ℝ) / 2 := by
    linarith
  have hprod_le_sum_sq_mul : a ^ a * b ^ b * c ^ c * d ^ d ≤ a * a + b * b + c * c + d * d := by
    simpa [mul_assoc] using
      (Real.geom_mean_le_arith_mean4_weighted ha_nonneg hb_nonneg hc_nonneg hd_nonneg
        ha_nonneg hb_nonneg hc_nonneg hd_nonneg h)
  have h_weight_sum_sq_le_one :
      (a + 2 * b + 3 * c + 4 * d) * (a * a + b * b + c * c + d * d) ≤ 1 := by
    let x : ℝ := a - b
    let y : ℝ := b - c
    let z : ℝ := c - d
    let L : ℝ := 4 * d
    let cert : ℝ :=
      3 * L ^ 2 + 8 * z + 12 * z * L + z * L ^ 2 +
      ((8 : ℝ) / 3) * y + ((32 : ℝ) / 3) * y * L + ((8 : ℝ) / 3) * y * L ^ 2 +
      16 * y * z + 4 * y * z * L + ((16 : ℝ) / 3) * y ^ 3 +
      9 * x * L ^ 2 + 40 * x * z * L + 48 * x * z ^ 2 +
      ((16 : ℝ) / 3) * x * y + ((44 : ℝ) / 3) * x * y * L +
      32 * x * y * z + ((32 : ℝ) / 3) * x * y ^ 2
    have hx : 0 ≤ x := by dsimp [x]; linarith
    have hy : 0 ≤ y := by dsimp [y]; linarith
    have hz : 0 ≤ z := by dsimp [z]; linarith
    have hL : 0 ≤ L := by dsimp [L]; positivity
    have hconstraint_zero : L + x + 2 * y + 3 * z - 1 = 0 := by
      dsimp [x, y, z, L]
      linarith
    have hfactor :
        8 * (1 - (a + 2 * b + 3 * c + 4 * d) * (a * a + b * b + c * c + d * d)) - cert =
          - (L + x + 2 * y + 3 * z - 1) *
            (15 * L ^ 2 + 48 * L * x + 56 * L * y + 84 * L * z + 24 * L +
              24 * x ^ 2 + 72 * x * y + 120 * x * z + 24 * x +
              80 * y ^ 2 + 168 * y * z + 40 * y + 144 * z ^ 2 + 48 * z + 24) / 3 := by
      dsimp [x, y, z, L, cert]
      ring
    have hcert_eq :
        8 * (1 - (a + 2 * b + 3 * c + 4 * d) * (a * a + b * b + c * c + d * d)) = cert := by
      rw [hconstraint_zero] at hfactor
      have hdiff_zero :
          8 * (1 - (a + 2 * b + 3 * c + 4 * d) * (a * a + b * b + c * c + d * d)) - cert = 0 := by
        simpa using hfactor
      linarith
    have hcert_nonneg : 0 ≤ cert := by
      dsimp [cert]
      positivity
    linarith
  have hmain_mul_le_one :
      (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) ≤ 1 := by
    have hmul_le :
        (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) ≤
          (a + 2 * b + 3 * c + 4 * d) * (a * a + b * b + c * c + d * d) := by
      exact mul_le_mul_of_nonneg_left hprod_le_sum_sq_mul (le_of_lt h_weight_pos)
    exact hmul_le.trans h_weight_sum_sq_le_one
  have htarget_reassoc :
      (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d =
        (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) := by
    ring
  rw [htarget_reassoc]
  exact hmain_mul_le_one
