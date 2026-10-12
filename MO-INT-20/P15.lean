import Mathlib

/-- AM-GM for three nonnegative reals whose product is one. -/
lemma amgm3_prod_one {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hprod : x * y * z = 1) : 3 ≤ x + y + z := by
  have hamgm := Real.geom_mean_le_arith_mean3_weighted
    (show 0 ≤ (1 / 3 : ℝ) by norm_num) (show 0 ≤ (1 / 3 : ℝ) by norm_num)
    (show 0 ≤ (1 / 3 : ℝ) by norm_num) hx hy hz
    (by norm_num : (1 / 3 : ℝ) + 1 / 3 + 1 / 3 = 1)
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have hroot : x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) = 1 := by
    rw [← Real.mul_rpow hx hy]
    rw [← Real.mul_rpow hxy hz]
    rw [hprod]
    norm_num
  nlinarith

theorem P15 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a ^ 2 + b ^ 2 + c ^ 2 + (a + b + c) ^ 2 ≤ 4) : 3 ≤ (a * b + 1) / (a + b) ^ 2 + (b * c + 1) / (b + c) ^ 2 + (c * a + 1) / (c + a) ^ 2 := by
  -- Every pairwise sum is positive, so its square is a nonzero denominator.
  have hab_add_pos : 0 < a + b := add_pos ha hb
  have hbc_add_pos : 0 < b + c := add_pos hb hc
  have hca_add_pos : 0 < c + a := add_pos hc ha
  have hab_sq_pos : 0 < (a + b) ^ 2 := pow_pos hab_add_pos 2
  have hbc_sq_pos : 0 < (b + c) ^ 2 := pow_pos hbc_add_pos 2
  have hca_sq_pos : 0 < (c + a) ^ 2 := pow_pos hca_add_pos 2

  -- Expanding (a+b+c)^2 turns the hypothesis into a²+b²+c²+ab+bc+ca ≤ 2.
  have hsq_prod_le : a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ≤ 2 := by
    nlinarith [h]

  -- Termwise lower bound: (ab+1)/(a+b)² ≥ 1/2 + (1/2)·(b+c)(c+a)/(a+b)².
  -- After clearing denominators this is exactly hsq_prod_le.
  have hterm_ab :
      1 / 2 + (1 / 2) * ((b + c) * (c + a) / (a + b) ^ 2) ≤ (a * b + 1) / (a + b) ^ 2 := by
    have hcleared : (a + b) ^ 2 + (b + c) * (c + a) ≤ 2 * (a * b + 1) := by
      nlinarith [hsq_prod_le]
    have hden : 0 < 2 * (a + b) ^ 2 := by positivity
    have hdiv := div_le_div_of_nonneg_right hcleared (le_of_lt hden)
    have hid_l : ((a + b) ^ 2 + (b + c) * (c + a)) / (2 * (a + b) ^ 2) =
        1 / 2 + (b + c) * (c + a) / (2 * (a + b) ^ 2) := by
      have h1 : (a + b) ^ 2 / (2 * (a + b) ^ 2) = 1 / 2 := by
        field_simp [ne_of_gt hab_add_pos]
      calc
        ((a + b) ^ 2 + (b + c) * (c + a)) / (2 * (a + b) ^ 2)
            = (a + b) ^ 2 / (2 * (a + b) ^ 2) + (b + c) * (c + a) / (2 * (a + b) ^ 2) := by
              ring
        _ = 1 / 2 + (b + c) * (c + a) / (2 * (a + b) ^ 2) := by
              rw [h1]
    have hid_r : (2 * (a * b + 1)) / (2 * (a + b) ^ 2) = (a * b + 1) / (a + b) ^ 2 := by
      field_simp [ne_of_gt hab_add_pos]
    have hid_half : (b + c) * (c + a) / (2 * (a + b) ^ 2) =
        (1 / 2) * ((b + c) * (c + a) / (a + b) ^ 2) := by
      field_simp [ne_of_gt hab_add_pos]
    nlinarith

  have hterm_bc :
      1 / 2 + (1 / 2) * ((c + a) * (a + b) / (b + c) ^ 2) ≤ (b * c + 1) / (b + c) ^ 2 := by
    have hcleared : (b + c) ^ 2 + (c + a) * (a + b) ≤ 2 * (b * c + 1) := by
      nlinarith [hsq_prod_le]
    have hden : 0 < 2 * (b + c) ^ 2 := by positivity
    have hdiv := div_le_div_of_nonneg_right hcleared (le_of_lt hden)
    have hid_l : ((b + c) ^ 2 + (c + a) * (a + b)) / (2 * (b + c) ^ 2) =
        1 / 2 + (c + a) * (a + b) / (2 * (b + c) ^ 2) := by
      have h1 : (b + c) ^ 2 / (2 * (b + c) ^ 2) = 1 / 2 := by
        field_simp [ne_of_gt hbc_add_pos]
      calc
        ((b + c) ^ 2 + (c + a) * (a + b)) / (2 * (b + c) ^ 2)
            = (b + c) ^ 2 / (2 * (b + c) ^ 2) + (c + a) * (a + b) / (2 * (b + c) ^ 2) := by
              ring
        _ = 1 / 2 + (c + a) * (a + b) / (2 * (b + c) ^ 2) := by
              rw [h1]
    have hid_r : (2 * (b * c + 1)) / (2 * (b + c) ^ 2) = (b * c + 1) / (b + c) ^ 2 := by
      field_simp [ne_of_gt hbc_add_pos]
    have hid_half : (c + a) * (a + b) / (2 * (b + c) ^ 2) =
        (1 / 2) * ((c + a) * (a + b) / (b + c) ^ 2) := by
      field_simp [ne_of_gt hbc_add_pos]
    nlinarith

  have hterm_ca :
      1 / 2 + (1 / 2) * ((a + b) * (b + c) / (c + a) ^ 2) ≤ (c * a + 1) / (c + a) ^ 2 := by
    have hcleared : (c + a) ^ 2 + (a + b) * (b + c) ≤ 2 * (c * a + 1) := by
      nlinarith [hsq_prod_le]
    have hden : 0 < 2 * (c + a) ^ 2 := by positivity
    have hdiv := div_le_div_of_nonneg_right hcleared (le_of_lt hden)
    have hid_l : ((c + a) ^ 2 + (a + b) * (b + c)) / (2 * (c + a) ^ 2) =
        1 / 2 + (a + b) * (b + c) / (2 * (c + a) ^ 2) := by
      have h1 : (c + a) ^ 2 / (2 * (c + a) ^ 2) = 1 / 2 := by
        field_simp [ne_of_gt hca_add_pos]
      calc
        ((c + a) ^ 2 + (a + b) * (b + c)) / (2 * (c + a) ^ 2)
            = (c + a) ^ 2 / (2 * (c + a) ^ 2) + (a + b) * (b + c) / (2 * (c + a) ^ 2) := by
              ring
        _ = 1 / 2 + (a + b) * (b + c) / (2 * (c + a) ^ 2) := by
              rw [h1]
    have hid_r : (2 * (c * a + 1)) / (2 * (c + a) ^ 2) = (c * a + 1) / (c + a) ^ 2 := by
      field_simp [ne_of_gt hca_add_pos]
    have hid_half : (a + b) * (b + c) / (2 * (c + a) ^ 2) =
        (1 / 2) * ((a + b) * (b + c) / (c + a) ^ 2) := by
      field_simp [ne_of_gt hca_add_pos]
    nlinarith

  -- The three "crossed" summands multiply to one, so AM-GM bounds their sum by 3.
  let x : ℝ := (b + c) * (c + a) / (a + b) ^ 2
  let y : ℝ := (c + a) * (a + b) / (b + c) ^ 2
  let z : ℝ := (a + b) * (b + c) / (c + a) ^ 2
  have hx_nonneg : 0 ≤ x := by dsimp [x]; positivity
  have hy_nonneg : 0 ≤ y := by dsimp [y]; positivity
  have hz_nonneg : 0 ≤ z := by dsimp [z]; positivity
  have hprod : x * y * z = 1 := by
    dsimp [x, y, z]
    field_simp [ne_of_gt hab_add_pos, ne_of_gt hbc_add_pos, ne_of_gt hca_add_pos]
  have hsum_ge : 3 ≤ x + y + z := amgm3_prod_one hx_nonneg hy_nonneg hz_nonneg hprod

  -- Summing the three termwise bounds gives the claim.
  have hP : 3 / 2 + (1 / 2) * (x + y + z) ≤
      (a * b + 1) / (a + b) ^ 2 + (b * c + 1) / (b + c) ^ 2 + (c * a + 1) / (c + a) ^ 2 := by
    dsimp [x, y, z]
    linarith [hterm_ab, hterm_bc, hterm_ca]

  linarith
