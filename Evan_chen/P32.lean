import Mathlib

open Real

lemma radon3 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x + y + z) / 9 ≤
      x ^ 3 / (z + 2 * y) ^ 2 + y ^ 3 / (x + 2 * z) ^ 2 + z ^ 3 / (y + 2 * x) ^ 2 := by
  let A := z + 2 * y
  let B := x + 2 * z
  let C := y + 2 * x
  let S := x + y + z
  let V := x ^ 2 / A + y ^ 2 / B + z ^ 2 / C
  let W := x ^ 3 / A ^ 2 + y ^ 3 / B ^ 2 + z ^ 3 / C ^ 2
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hS : 0 < S := by
    dsimp [S]
    positivity
  have hD : A + B + C = 3 * S := by
    dsimp [A, B, C, S]
    ring
  have hcauchy1_raw : S ^ 2 / (A + B + C) ≤ V := by
    have h := Finset.sq_sum_div_le_sum_sq_div (s := Finset.univ) (f := ![x, y, z])
      (g := ![A, B, C]) (by
        intro i hi
        fin_cases i <;> simp [hA, hB, hC])
    simpa [Fin.sum_univ_three, S, V, A, B, C] using h
  have hcauchy1 : S / 3 ≤ V := by
    have hleft : S ^ 2 / (A + B + C) = S / 3 := by
      rw [hD]
      field_simp [hS.ne']
    rwa [hleft] at hcauchy1_raw
  have hcauchy2_raw : V ^ 2 / S ≤ W := by
    have h := Finset.sq_sum_div_le_sum_sq_div (s := Finset.univ)
      (f := ![x ^ 2 / A, y ^ 2 / B, z ^ 2 / C])
      (g := ![x, y, z]) (by
        intro i hi
        fin_cases i <;> simp [hx, hy, hz])
    have hright :
        (x ^ 2 / A) ^ 2 / x + (y ^ 2 / B) ^ 2 / y + (z ^ 2 / C) ^ 2 / z = W := by
      dsimp [W]
      field_simp [hx.ne', hy.ne', hz.ne', hA.ne', hB.ne', hC.ne']
    simpa [Fin.sum_univ_three, V, S, hright] using h
  have hSdiv_nonneg : 0 ≤ S / 3 := by
    positivity
  have hV_nonneg : 0 ≤ V := le_trans hSdiv_nonneg hcauchy1
  have hsq : (S / 3) ^ 2 ≤ V ^ 2 := by
    exact (sq_le_sq₀ hSdiv_nonneg hV_nonneg).2 hcauchy1
  have hdiv : (S / 3) ^ 2 / S ≤ V ^ 2 / S := by
    exact div_le_div_of_nonneg_right hsq hS.le
  have hleft : (S / 3) ^ 2 / S = S / 9 := by
    field_simp [hS.ne']
    ring
  have hSW : S / 9 ≤ W := by
    rw [← hleft]
    exact le_trans hdiv hcauchy2_raw
  simpa [S, W, A, B, C] using hSW

lemma amgm3_product_one {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) : 3 ≤ x + y + z := by
  have hxy : 0 < x * y := mul_pos hx hy
  have h_amgm0 :
      x ^ (1 / (3 : ℝ)) * y ^ (1 / (3 : ℝ)) * z ^ (1 / (3 : ℝ)) ≤
        (1 / (3 : ℝ)) * x + (1 / (3 : ℝ)) * y + (1 / (3 : ℝ)) * z := by
    exact Real.geom_mean_le_arith_mean3_weighted
      (by norm_num) (by norm_num) (by norm_num)
      (le_of_lt hx) (le_of_lt hy) (le_of_lt hz)
      (by norm_num)
  have hprod_rpow :
      x ^ (1 / (3 : ℝ)) * y ^ (1 / (3 : ℝ)) * z ^ (1 / (3 : ℝ)) = 1 := by
    calc
      x ^ (1 / (3 : ℝ)) * y ^ (1 / (3 : ℝ)) * z ^ (1 / (3 : ℝ))
          = (x * y) ^ (1 / (3 : ℝ)) * z ^ (1 / (3 : ℝ)) := by
              rw [← Real.mul_rpow (le_of_lt hx) (le_of_lt hy)]
      _ = (x * y * z) ^ (1 / (3 : ℝ)) := by
              symm
              exact Real.mul_rpow (le_of_lt hxy) (le_of_lt hz)
      _ = 1 := by
              rw [hxyz]
              norm_num
  rw [hprod_rpow] at h_amgm0
  nlinarith

theorem P32 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 1 / 3 ≤ (1 / (a ^ 5 * (b + 2 * c) ^ 2)) + (1 / (b ^ 5 * (c + 2 * a) ^ 2)) + (1 / (c ^ 5 * (a + 2 * b) ^ 2)) := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hb_add_2c_pos : 0 < b + 2 * c := by positivity
  have hc_add_2a_pos : 0 < c + 2 * a := by positivity
  have ha_add_2b_pos : 0 < a + 2 * b := by positivity
  have hden₁_pos : 0 < a ^ 5 * (b + 2 * c) ^ 2 := by positivity
  have hden₂_pos : 0 < b ^ 5 * (c + 2 * a) ^ 2 := by positivity
  have hden₃_pos : 0 < c ^ 5 * (a + 2 * b) ^ 2 := by positivity
  have hinv_a_eq_bc : a⁻¹ = b * c := by
    have hmul : a * (b * c) = 1 := by
      rw [← h]
      ring
    apply mul_left_cancel₀ ha_ne
    calc
      a * a⁻¹ = 1 := mul_inv_cancel₀ ha_ne
      _ = a * (b * c) := by rw [hmul]
  have hinv_b_eq_ca : b⁻¹ = c * a := by
    have hmul : b * (c * a) = 1 := by
      rw [← h]
      ring
    apply mul_left_cancel₀ hb_ne
    calc
      b * b⁻¹ = 1 := mul_inv_cancel₀ hb_ne
      _ = b * (c * a) := by rw [hmul]
  have hinv_c_eq_ab : c⁻¹ = a * b := by
    have hmul : c * (a * b) = 1 := by
      rw [← h]
      ring
    apply mul_left_cancel₀ hc_ne
    calc
      c * c⁻¹ = 1 := mul_inv_cancel₀ hc_ne
      _ = c * (a * b) := by rw [hmul]
  let x := 1 / a
  let y := 1 / b
  let z := 1 / c
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hy : 0 < y := by
    dsimp [y]
    positivity
  have hz : 0 < z := by
    dsimp [z]
    positivity
  have hxyz : x * y * z = 1 := by
    dsimp [x, y, z]
    field_simp [ha.ne', hb.ne', hc.ne']
    exact h.symm
  have habc_sq : a ^ 2 * b ^ 2 * c ^ 2 = 1 := by
    calc
      a ^ 2 * b ^ 2 * c ^ 2 = (a * b * c) ^ 2 := by ring
      _ = 1 := by
        rw [h]
        norm_num
  have hsum : 3 ≤ x + y + z := amgm3_product_one hx hy hz hxyz
  have hradon := radon3 hx hy hz
  have hthird : (1 : ℝ) / 3 ≤ (x + y + z) / 9 := by
    nlinarith [hsum]
  have htrans :
      (1 : ℝ) / 3 ≤
        x ^ 3 / (z + 2 * y) ^ 2 + y ^ 3 / (x + 2 * z) ^ 2 + z ^ 3 / (y + 2 * x) ^ 2 := by
    exact le_trans hthird hradon
  dsimp [x, y, z] at htrans
  convert htrans using 1
  all_goals
    field_simp [ha.ne', hb.ne', hc.ne']
    exact habc_sq.symm
