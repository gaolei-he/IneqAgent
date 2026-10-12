import Mathlib

open Real

local macro_rules
  | `($x:term ^ (1 / 3)) => `($x ^ (1 / 3 : ℝ))

theorem P28 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 8 * (a * b * c) ^ (1 / 3) + ((a ^ 3 + b ^ 3 + c ^ 3) / 3) ^ (1 / 3) ≤ 3 * (a + b + c) := by
  let g : ℝ := (a * b * c) ^ (1 / 3 : ℝ)
  let m : ℝ := (a ^ 3 + b ^ 3 + c ^ 3) / 3
  let q : ℝ := m ^ (1 / 3 : ℝ)
  have habc_nonneg : 0 ≤ a * b * c := by positivity
  have habc_pos : 0 < a * b * c := by positivity
  have hg_nonneg : 0 ≤ g := by
    dsimp [g]
    exact Real.rpow_nonneg habc_nonneg _
  have hg_pos : 0 < g := by
    dsimp [g]
    exact Real.rpow_pos_of_pos habc_pos _
  have hg3 : g ^ 3 = a * b * c := by
    dsimp [g]
    have hinv : (1 / 3 : ℝ) = ((3 : ℕ)⁻¹ : ℝ) := by norm_num
    rw [hinv]
    exact Real.rpow_inv_natCast_pow habc_nonneg (by norm_num : (3 : ℕ) ≠ 0)
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    positivity
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact Real.rpow_nonneg hm_nonneg _
  have hq3 : q ^ 3 = m := by
    dsimp [q]
    have hinv : (1 / 3 : ℝ) = ((3 : ℕ)⁻¹ : ℝ) := by norm_num
    rw [hinv]
    exact Real.rpow_inv_natCast_pow hm_nonneg (by norm_num : (3 : ℕ) ≠ 0)
  have hgm_le_sum : 3 * g ≤ a + b + c := by
    have ham := Real.geom_mean_le_arith_mean3_weighted
      (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
      (p₁ := a) (p₂ := b) (p₃ := c)
      (by norm_num) (by norm_num) (by norm_num)
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
      (by norm_num : (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1)
    have hmul : a ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = g := by
      dsimp [g]
      rw [← Real.mul_rpow (le_of_lt ha) (le_of_lt hb),
        ← Real.mul_rpow (mul_nonneg (le_of_lt ha) (le_of_lt hb)) (le_of_lt hc)]
    rw [hmul] at ham
    nlinarith [ham]
  have hp_le : 3 * g ^ 2 ≤ a * b + b * c + c * a := by
    have ham := Real.geom_mean_le_arith_mean3_weighted
      (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
      (p₁ := a * b) (p₂ := b * c) (p₃ := c * a)
      (by norm_num) (by norm_num) (by norm_num)
      (mul_nonneg (le_of_lt ha) (le_of_lt hb))
      (mul_nonneg (le_of_lt hb) (le_of_lt hc))
      (mul_nonneg (le_of_lt hc) (le_of_lt ha))
      (by norm_num : (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1)
    have hprod : (a * b) ^ (1 / 3 : ℝ) * (b * c) ^ (1 / 3 : ℝ) *
        (c * a) ^ (1 / 3 : ℝ) = ((a * b) * (b * c) * (c * a)) ^ (1 / 3 : ℝ) := by
      rw [← Real.mul_rpow (mul_nonneg (le_of_lt ha) (le_of_lt hb))
          (mul_nonneg (le_of_lt hb) (le_of_lt hc)),
        ← Real.mul_rpow
          (mul_nonneg (mul_nonneg (le_of_lt ha) (le_of_lt hb))
            (mul_nonneg (le_of_lt hb) (le_of_lt hc)))
          (mul_nonneg (le_of_lt hc) (le_of_lt ha))]
    rw [hprod] at ham
    have hprod_eq : ((a * b) * (b * c) * (c * a)) ^ (1 / 3 : ℝ) = g ^ 2 := by
      have hnonneg : 0 ≤ (a * b) * (b * c) * (c * a) := by positivity
      apply (pow_left_inj₀ (Real.rpow_nonneg hnonneg _) (pow_nonneg hg_nonneg _)
        (by norm_num : (3 : ℕ) ≠ 0)).mp
      have hinv : (1 / 3 : ℝ) = ((3 : ℕ)⁻¹ : ℝ) := by norm_num
      rw [hinv]
      rw [Real.rpow_inv_natCast_pow hnonneg (by norm_num : (3 : ℕ) ≠ 0)]
      calc
        (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 := by ring
        _ = (g ^ 3) ^ 2 := by rw [hg3]
        _ = (g ^ 2) ^ 3 := by ring
    rw [hprod_eq] at ham
    nlinarith [ham]
  have hR_nonneg : 0 ≤ 3 * (a + b + c) - 8 * g := by
    nlinarith [hgm_le_sum, hg_nonneg]
  have hm_bound : m ≤ (3 * (a + b + c) - 8 * g) ^ 3 := by
    have hsum_nonneg : 0 ≤ a + b + c := by positivity
    have hid : a ^ 3 + b ^ 3 + c ^ 3 =
        (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) + 3 * g ^ 3 := by
      nlinarith [hg3]
    have hfirst : m ≤ ((a + b + c) ^ 3 - 9 * (a + b + c) * g ^ 2 + 3 * g ^ 3) / 3 := by
      dsimp [m]
      nlinarith [hid, hsum_nonneg, hp_le]
    have hsecond : ((a + b + c) ^ 3 - 9 * (a + b + c) * g ^ 2 + 3 * g ^ 3) / 3 ≤
        (3 * (a + b + c) - 8 * g) ^ 3 := by
      have ht : 0 ≤ (a + b + c) - 3 * g := by nlinarith [hgm_le_sum]
      have hA : 0 ≤ 3 * g + 4 * ((a + b + c) - 3 * g) := by nlinarith [hg_nonneg, ht]
      have hB : 0 ≤ 3 * g + 20 * ((a + b + c) - 3 * g) := by nlinarith [hg_nonneg, ht]
      have hprod_nonneg : 0 ≤ ((a + b + c) - 3 * g) *
          (3 * g + 4 * ((a + b + c) - 3 * g)) *
          (3 * g + 20 * ((a + b + c) - 3 * g)) := by positivity
      nlinarith [hprod_nonneg]
    exact hfirst.trans hsecond
  have hq_le : q ≤ 3 * (a + b + c) - 8 * g := by
    apply (pow_le_pow_iff_left₀ hq_nonneg hR_nonneg (by norm_num : (3 : ℕ) ≠ 0)).mp
    rw [hq3]
    exact hm_bound
  have hgoal : 8 * g + q ≤ 3 * (a + b + c) := by nlinarith [hq_le]
  simpa [g, q, m] using hgoal
