import Mathlib

open Real

theorem P22 {a b : ℝ} (ha : a > 0) (hb : b > 0) (h : a + b < 6): 1 / sqrt (1 + a) + 1 / sqrt (1 + b) + sqrt (a * b) / sqrt (a * b + 8) ≤ 2 := by
  have one_div_sqrt_le :
      ∀ t : ℝ, 0 ≤ t → 1 / sqrt (1 + t) ≤ 1 - t / (2 * (1 + t)) := by
    intro t ht
    have hpos : 0 < 1 + t := by linarith
    have hspos : 0 < sqrt (1 + t) := Real.sqrt_pos.2 hpos
    have hsq : (sqrt (1 + t)) ^ 2 = 1 + t := Real.sq_sqrt hpos.le
    have htwo : 2 * sqrt (1 + t) ≤ (1 + t) + 1 := by
      nlinarith [sq_nonneg (sqrt (1 + t) - 1), hsq]
    calc
      1 / sqrt (1 + t) = (2 * sqrt (1 + t)) / (2 * (1 + t)) := by
        field_simp [hspos.ne', hpos.ne']
        exact hsq.symm
      _ ≤ ((1 + t) + 1) / (2 * (1 + t)) := by
        exact div_le_div_of_nonneg_right htwo (by positivity)
      _ = 1 - t / (2 * (1 + t)) := by
        field_simp [hpos.ne']
        ring
  have ha_nonneg : 0 ≤ a := le_of_lt ha
  have hb_nonneg : 0 ≤ b := le_of_lt hb
  have h_one_a_pos : 0 < 1 + a := by linarith
  have h_one_b_pos : 0 < 1 + b := by linarith
  have hab_pos : 0 < a * b := mul_pos ha hb
  have hab_nonneg : 0 ≤ a * b := le_of_lt hab_pos
  have hden_ab_pos : 0 < sqrt (a * b + 8) := by
    exact Real.sqrt_pos.2 (by positivity)
  have hden_prod_pos : 0 < sqrt ((1 + a) * (1 + b)) := by
    exact Real.sqrt_pos.2 (by positivity)
  have hprod_le : (1 + a) * (1 + b) ≤ a * b + 8 := by
    nlinarith
  have hsqrt_prod_le : sqrt ((1 + a) * (1 + b)) ≤ sqrt (a * b + 8) := by
    exact Real.sqrt_le_sqrt hprod_le
  let x : ℝ := sqrt a / sqrt (1 + a)
  let y : ℝ := sqrt b / sqrt (1 + b)
  have hx_sq : x ^ 2 = a / (1 + a) := by
    dsimp [x]
    rw [div_pow, Real.sq_sqrt ha_nonneg, Real.sq_sqrt h_one_a_pos.le]
  have hy_sq : y ^ 2 = b / (1 + b) := by
    dsimp [y]
    rw [div_pow, Real.sq_sqrt hb_nonneg, Real.sq_sqrt h_one_b_pos.le]
  have hxy_avg : x * y ≤ (a / (1 + a) + b / (1 + b)) / 2 := by
    have hbase : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg (x - y)]
    nlinarith [hx_sq, hy_sq]
  have hsqrt_mul :
      sqrt (a * b) / sqrt ((1 + a) * (1 + b)) = x * y := by
    dsimp [x, y]
    have hnum : sqrt (a * b) = sqrt a * sqrt b := by
      rw [Real.sqrt_mul ha_nonneg b]
    have hden : sqrt ((1 + a) * (1 + b)) = sqrt (1 + a) * sqrt (1 + b) := by
      rw [Real.sqrt_mul h_one_a_pos.le (1 + b)]
    rw [hnum, hden]
    ring_nf
  have hthird_le_xy : sqrt (a * b) / sqrt (a * b + 8) ≤ x * y := by
    rw [← hsqrt_mul]
    exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hden_prod_pos hsqrt_prod_le
  have hthird_bound :
      sqrt (a * b) / sqrt (a * b + 8) ≤
        a / (2 * (1 + a)) + b / (2 * (1 + b)) := by
    have havg_rewrite :
        (a / (1 + a) + b / (1 + b)) / 2 =
          a / (2 * (1 + a)) + b / (2 * (1 + b)) := by
      field_simp [h_one_a_pos.ne', h_one_b_pos.ne']
    calc
      sqrt (a * b) / sqrt (a * b + 8) ≤ x * y := hthird_le_xy
      _ ≤ (a / (1 + a) + b / (1 + b)) / 2 := hxy_avg
      _ = a / (2 * (1 + a)) + b / (2 * (1 + b)) := havg_rewrite
  have hfirst : 1 / sqrt (1 + a) ≤ 1 - a / (2 * (1 + a)) := by
    exact one_div_sqrt_le a ha_nonneg
  have hsecond : 1 / sqrt (1 + b) ≤ 1 - b / (2 * (1 + b)) := by
    exact one_div_sqrt_le b hb_nonneg
  linarith
