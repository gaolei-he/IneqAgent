import Mathlib

open Real

noncomputable local instance realHDivDefault : HDiv ℝ ℝ ℝ := inferInstance
attribute [default_instance 2000] realHDivDefault

private lemma radical_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < x ^ 2 - x * y + y ^ 2 := by
  nlinarith [sq_nonneg (x - y), mul_pos hx hy]

private lemma sqrt_radical_le_sum {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    sqrt (x ^ 2 - x * y + y ^ 2) ≤ x + y := by
  have hqle : x ^ 2 - x * y + y ^ 2 ≤ (x + y) ^ 2 := by
    nlinarith [mul_pos hx hy]
  have hsq : sqrt (x ^ 2 - x * y + y ^ 2) ≤ sqrt ((x + y) ^ 2) := by
    exact Real.sqrt_le_sqrt hqle
  calc
    sqrt (x ^ 2 - x * y + y ^ 2) ≤ sqrt ((x + y) ^ 2) := hsq
    _ = |x + y| := Real.sqrt_sq_eq_abs (x + y)
    _ = x + y := by rw [abs_of_pos (add_pos hx hy)]

private lemma sum_sqrt_sq_le_three_sum {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    (sqrt x + sqrt y + sqrt z) ^ 2 ≤ 3 * (x + y + z) := by
  have hux : (sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have huy : (sqrt y) ^ 2 = y := Real.sq_sqrt hy
  have huz : (sqrt z) ^ 2 = z := Real.sq_sqrt hz
  have h := (show (sqrt x + sqrt y + sqrt z) ^ 2 ≤
      3 * ((sqrt x) ^ 2 + (sqrt y) ^ 2 + (sqrt z) ^ 2) by
      nlinarith [sq_nonneg (sqrt x - sqrt y), sq_nonneg (sqrt y - sqrt z),
        sq_nonneg (sqrt z - sqrt x)])
  nlinarith

theorem P36 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h1 : a ^ 2 - a * b + b ^ 2 > 0) (h2 : b ^ 2 - b * c + c ^ 2 > 0) (h3 : c ^ 2 - c * a + a ^ 2 > 0) : sqrt (a ^ 2 - a * b + b ^ 2) + sqrt (b ^ 2 - b * c + c ^ 2) + sqrt (c ^ 2 - c * a + a ^ 2) + 9 * (a * b * c) ^ (1 / 3) ≤ 4 * (a + b + c) := by
  let g : ℝ := (a * b * c) ^ (1 / 3 : ℝ)
  have habc_pos : 0 < a * b * c := by positivity
  have hg_pos : 0 < g := by
    dsimp [g]
    exact Real.rpow_pos_of_pos habc_pos _
  have hg_nonneg : 0 ≤ g := le_of_lt hg_pos
  have hg_ne : g ≠ 0 := ne_of_gt hg_pos
  have hg3 : g ^ 3 = a * b * c := by
    dsimp [g]
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow (x := a * b * c) (n := 3) (le_of_lt habc_pos)
        (by norm_num : (3 : ℕ) ≠ 0))
  have radical_bound :
      ∀ {x y : ℝ}, x > 0 → y > 0 →
        sqrt (x ^ 2 - x * y + y ^ 2) ≤
          (5 / 4 : ℝ) * (x + y) - 3 * (x * y) / (x + y) := by
    intro x y hx hy
    have hsum_pos : 0 < x + y := by linarith
    have hsum_ne : x + y ≠ 0 := ne_of_gt hsum_pos
    have hsum_sq_pos : 0 < (x + y) ^ 2 := sq_pos_of_pos hsum_pos
    have hxy_pos : 0 < x * y := by positivity
    have hright_mul :
        0 ≤ ((5 / 4 : ℝ) * (x + y) - 3 * (x * y) / (x + y)) * (x + y) := by
      field_simp [hsum_ne]
      nlinarith [sq_nonneg (x - y), hxy_pos.le]
    have hright_nonneg :
        0 ≤ (5 / 4 : ℝ) * (x + y) - 3 * (x * y) / (x + y) :=
      (mul_nonneg_iff_of_pos_right hsum_pos).mp hright_mul
    have hsquare_mul :
        0 ≤
          (((5 / 4 : ℝ) * (x + y) - 3 * (x * y) / (x + y)) ^ 2 -
              (x ^ 2 - x * y + y ^ 2)) * (x + y) ^ 2 := by
      field_simp [hsum_ne]
      nlinarith [sq_nonneg (x - y)]
    have hsquare_nonneg :
        0 ≤
          ((5 / 4 : ℝ) * (x + y) - 3 * (x * y) / (x + y)) ^ 2 -
              (x ^ 2 - x * y + y ^ 2) :=
      (mul_nonneg_iff_of_pos_right hsum_sq_pos).mp hsquare_mul
    have hsquare :
        x ^ 2 - x * y + y ^ 2 ≤
          ((5 / 4 : ℝ) * (x + y) - 3 * (x * y) / (x + y)) ^ 2 := by
      nlinarith
    exact Real.sqrt_le_iff.mpr ⟨hright_nonneg, hsquare⟩
  have hrad_ab := radical_bound ha hb
  have hrad_bc := radical_bound hb hc
  have hrad_ca := radical_bound hc ha
  have hrad_sum :
      sqrt (a ^ 2 - a * b + b ^ 2) + sqrt (b ^ 2 - b * c + c ^ 2) +
          sqrt (c ^ 2 - c * a + a ^ 2) ≤
        (5 / 2 : ℝ) * (a + b + c) -
          3 * (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) := by
    calc
      sqrt (a ^ 2 - a * b + b ^ 2) + sqrt (b ^ 2 - b * c + c ^ 2) +
          sqrt (c ^ 2 - c * a + a ^ 2)
          ≤ ((5 / 4 : ℝ) * (a + b) - 3 * (a * b) / (a + b)) +
              ((5 / 4 : ℝ) * (b + c) - 3 * (b * c) / (b + c)) +
                ((5 / 4 : ℝ) * (c + a) - 3 * (c * a) / (c + a)) := by
            linarith
      _ = (5 / 2 : ℝ) * (a + b + c) -
          3 * (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) := by
            ring
  have hg_as_product :
      a ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = g := by
    dsimp [g]
    rw [← Real.mul_rpow (le_of_lt ha) (le_of_lt hb)]
    rw [← Real.mul_rpow (mul_nonneg (le_of_lt ha) (le_of_lt hb)) (le_of_lt hc)]
  have hp_ge : 3 * g ≤ a + b + c := by
    have hamgm :
        a ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) ≤
          (1 / 3 : ℝ) * a + (1 / 3 : ℝ) * b + (1 / 3 : ℝ) * c := by
      exact Real.geom_mean_le_arith_mean3_weighted
        (by norm_num) (by norm_num) (by norm_num)
        (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
        (by norm_num)
    have : g ≤ (a + b + c) / 3 := by
      calc
        g = a ^ (1 / 3 : ℝ) * b ^ (1 / 3 : ℝ) * c ^ (1 / 3 : ℝ) := hg_as_product.symm
        _ ≤ (1 / 3 : ℝ) * a + (1 / 3 : ℝ) * b + (1 / 3 : ℝ) * c := hamgm
        _ = (a + b + c) / 3 := by ring
    nlinarith
  have hq_ge : 3 * g ^ 2 ≤ a * b + b * c + c * a := by
    have hab_nonneg : 0 ≤ a * b := by positivity
    have hbc_nonneg : 0 ≤ b * c := by positivity
    have hca_nonneg : 0 ≤ c * a := by positivity
    have hpair_product :
        (a * b) ^ (1 / 3 : ℝ) * (b * c) ^ (1 / 3 : ℝ) *
            (c * a) ^ (1 / 3 : ℝ) = g ^ 2 := by
      have hleft :
          (a * b) ^ (1 / 3 : ℝ) * (b * c) ^ (1 / 3 : ℝ) *
              (c * a) ^ (1 / 3 : ℝ) =
            ((a * b) * (b * c) * (c * a)) ^ (1 / 3 : ℝ) := by
        rw [← Real.mul_rpow hab_nonneg hbc_nonneg]
        rw [← Real.mul_rpow (mul_nonneg hab_nonneg hbc_nonneg) hca_nonneg]
      have hprod_eq : (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 := by ring
      have hg2 :
          g ^ 2 = ((a * b * c) ^ 2) ^ (1 / 3 : ℝ) := by
        dsimp [g]
        rw [← Real.rpow_mul_natCast (le_of_lt habc_pos) (y := (1 / 3 : ℝ)) (n := 2)]
        rw [← Real.rpow_natCast_mul (le_of_lt habc_pos) (n := 2) (z := (1 / 3 : ℝ))]
        congr 1
        norm_num
      rw [hleft, hprod_eq, hg2]
    have hamgm :
        (a * b) ^ (1 / 3 : ℝ) * (b * c) ^ (1 / 3 : ℝ) *
            (c * a) ^ (1 / 3 : ℝ) ≤
          (1 / 3 : ℝ) * (a * b) + (1 / 3 : ℝ) * (b * c) +
            (1 / 3 : ℝ) * (c * a) := by
      exact Real.geom_mean_le_arith_mean3_weighted
        (by norm_num) (by norm_num) (by norm_num)
        hab_nonneg hbc_nonneg hca_nonneg
        (by norm_num)
    have : g ^ 2 ≤ (a * b + b * c + c * a) / 3 := by
      calc
        g ^ 2 =
            (a * b) ^ (1 / 3 : ℝ) * (b * c) ^ (1 / 3 : ℝ) *
              (c * a) ^ (1 / 3 : ℝ) := hpair_product.symm
        _ ≤ (1 / 3 : ℝ) * (a * b) + (1 / 3 : ℝ) * (b * c) +
            (1 / 3 : ℝ) * (c * a) := hamgm
        _ = (a * b + b * c + c * a) / 3 := by ring
    nlinarith
  have htangent_aux :
      3 * g ≤
        (a + b + c) / 2 +
          (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) := by
    let p : ℝ := a + b + c
    let q : ℝ := a * b + b * c + c * a
    have hp_pos : 0 < p := by dsimp [p]; positivity
    have hq_pos : 0 < q := by dsimp [q]; positivity
    have hp_ge' : 3 * g ≤ p := by simpa [p] using hp_ge
    have hq_ge' : 3 * g ^ 2 ≤ q := by simpa [q] using hq_ge
    have hp_sub_nonneg : 0 ≤ p - 3 * g := by linarith
    have hq_sub_nonneg : 0 ≤ q - 3 * g ^ 2 := by linarith
    have hpq_den_pos : 0 < p * q - g ^ 3 := by
      dsimp [p, q]
      rw [hg3]
      nlinarith [ha, hb, hc, mul_pos ha hb, mul_pos hb hc, mul_pos hc ha]
    have hden_abc_pos : 0 < (a + b) * (b + c) * (c + a) := by positivity
    have hden_eq : (a + b) * (b + c) * (c + a) = p * q - g ^ 3 := by
      dsimp [p, q]
      rw [hg3]
      ring
    have hT_eq :
        a * b / (a + b) + b * c / (b + c) + c * a / (c + a) =
          (p * g ^ 3 + q ^ 2) / (p * q - g ^ 3) := by
      rw [← hden_eq]
      field_simp [show a + b ≠ 0 by positivity, show b + c ≠ 0 by positivity,
        show c + a ≠ 0 by positivity, ne_of_gt hden_abc_pos]
      dsimp [p, q]
      rw [hg3]
      ring
    have hcleared_nonneg :
        0 ≤ (p / 2 + (p * g ^ 3 + q ^ 2) / (p * q - g ^ 3) - 3 * g) *
            (p * q - g ^ 3) := by
      have hpoly :
          0 ≤ 6 * g ^ 4 + g ^ 3 * p - 6 * g * p * q + p ^ 2 * q + 2 * q ^ 2 := by
        have h1 : 0 ≤ g ^ 3 * (p - 3 * g) :=
          mul_nonneg (pow_nonneg hg_nonneg 3) hp_sub_nonneg
        have h2 : 0 ≤ 3 * g ^ 2 * (p - 3 * g) ^ 2 := by positivity
        have h3 : 0 ≤ 3 * g ^ 2 * (q - 3 * g ^ 2) :=
          mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hg_nonneg 2)) hq_sub_nonneg
        have h4 : 0 ≤ (p - 3 * g) ^ 2 * (q - 3 * g ^ 2) :=
          mul_nonneg (sq_nonneg (p - 3 * g)) hq_sub_nonneg
        have h5 : 0 ≤ 2 * (q - 3 * g ^ 2) ^ 2 := by positivity
        have hid :
            6 * g ^ 4 + g ^ 3 * p - 6 * g * p * q + p ^ 2 * q + 2 * q ^ 2 =
              g ^ 3 * (p - 3 * g) + 3 * g ^ 2 * (p - 3 * g) ^ 2 +
                3 * g ^ 2 * (q - 3 * g ^ 2) +
                  (p - 3 * g) ^ 2 * (q - 3 * g ^ 2) +
                    2 * (q - 3 * g ^ 2) ^ 2 := by
          ring
        rw [hid]
        linarith
      have hidentity :
          2 * ((p / 2 + (p * g ^ 3 + q ^ 2) / (p * q - g ^ 3) - 3 * g) *
              (p * q - g ^ 3)) =
            6 * g ^ 4 + g ^ 3 * p - 6 * g * p * q + p ^ 2 * q + 2 * q ^ 2 := by
        field_simp [ne_of_gt hpq_den_pos]
        ring
      linarith
    have hbase :
        0 ≤ p / 2 + (p * g ^ 3 + q ^ 2) / (p * q - g ^ 3) - 3 * g :=
      (mul_nonneg_iff_of_pos_right hpq_den_pos).mp hcleared_nonneg
    have hbase_le :
        3 * g ≤ p / 2 + (p * g ^ 3 + q ^ 2) / (p * q - g ^ 3) := by
      linarith
    simpa [p, hT_eq] using hbase_le
  have hfinal_bound :
      sqrt (a ^ 2 - a * b + b ^ 2) + sqrt (b ^ 2 - b * c + c ^ 2) +
          sqrt (c ^ 2 - c * a + a ^ 2) + 9 * g ≤ 4 * (a + b + c) := by
    nlinarith [hrad_sum, htangent_aux]
  simpa [g] using hfinal_bound
