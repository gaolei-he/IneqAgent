import Mathlib

lemma P6_amgm_aux {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    a ^ 3 / ((1 + b) * (1 + c)) + (1 + b) / 8 + (1 + c) / 8 ≥ 3 * a / 4 := by
  let u : ℝ := a ^ 3 / ((1 + b) * (1 + c))
  let v : ℝ := (1 + b) / 8
  let w : ℝ := (1 + c) / 8
  have hu : 0 < u := by
    dsimp [u]
    positivity
  have hv : 0 < v := by
    dsimp [v]
    positivity
  have hw : 0 < w := by
    dsimp [w]
    positivity
  have hamgm := Real.geom_mean_le_arith_mean3_weighted
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
      (le_of_lt hu) (le_of_lt hv) (le_of_lt hw)
      (by norm_num : (1 : ℝ) / 3 + (1 : ℝ) / 3 + (1 : ℝ) / 3 = 1)
  have hgeom : u ^ (3 : ℝ)⁻¹ * v ^ (3 : ℝ)⁻¹ * w ^ (3 : ℝ)⁻¹ =
      (u * v * w) ^ (3 : ℝ)⁻¹ := by
    rw [← Real.mul_rpow (le_of_lt hu) (le_of_lt hv)]
    rw [← Real.mul_rpow (mul_nonneg (le_of_lt hu) (le_of_lt hv)) (le_of_lt hw)]
  have hden : (1 + b) * (1 + c) ≠ 0 := by positivity
  have hprod : u * v * w = (a / 4) ^ 3 := by
    dsimp [u, v, w]
    field_simp [hden]
    ring
  have ha4 : 0 ≤ a / 4 := by positivity
  simp only [one_div] at hamgm
  rw [hgeom, hprod] at hamgm
  have hroot : ((a / 4) ^ 3) ^ (3⁻¹ : ℝ) = a / 4 := by
    exact Real.pow_rpow_inv_natCast ha4 (by norm_num : (3 : ℕ) ≠ 0)
  rw [hroot] at hamgm
  change 3 * a / 4 ≤ u + v + w
  nlinarith

lemma P6_amgm3_sum {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a * b * c = 1) : 3 ≤ a + b + c := by
  have hamgm3 := Real.geom_mean_le_arith_mean3_weighted
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
      (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 3)
      (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
      (by norm_num : (1 : ℝ) / 3 + (1 : ℝ) / 3 + (1 : ℝ) / 3 = 1)
  have hgeom : a ^ (3 : ℝ)⁻¹ * b ^ (3 : ℝ)⁻¹ * c ^ (3 : ℝ)⁻¹ =
      (a * b * c) ^ (3 : ℝ)⁻¹ := by
    rw [← Real.mul_rpow (le_of_lt ha) (le_of_lt hb)]
    rw [← Real.mul_rpow (mul_nonneg (le_of_lt ha) (le_of_lt hb)) (le_of_lt hc)]
  simp only [one_div] at hamgm3
  rw [hgeom, h] at hamgm3
  simp only [Real.one_rpow] at hamgm3
  nlinarith

theorem P6 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : 3 / 4 ≤ a ^ 3 / ((1 + b) * (1 + c)) + b ^ 3 / ((1 + c) * (1 + a)) + c ^ 3 / ((1 + a) * (1 + b)) := by
  have h1 := P6_amgm_aux ha hb hc
  have h2 := P6_amgm_aux hb hc ha
  have h3 := P6_amgm_aux hc ha hb
  have hsum := P6_amgm3_sum ha hb hc h
  nlinarith
