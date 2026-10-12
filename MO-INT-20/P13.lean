import Mathlib

lemma rpow_neg_two_eq_one_div_sq {x : ℝ} (hx : 0 < x) :
    x ^ (-2 : ℝ) = 1 / x ^ 2 := by
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num]
  rw [Real.rpow_neg hx.le]
  simp [one_div]

lemma polynomial_key_for_P13 {t q : ℝ} (ht : 9 ≤ t) (hq : 3 ≤ q) :
    0 ≤ 3 * (2 * t^2 + t * q + q)^2 - 16 * t * (9 * t^2 + 2 * t * q + q^2 - 8 * q) := by
  have hC : 0 ≤ 3 * t^2 - 10 * t + 3 := by
    nlinarith [sq_nonneg (t - 9)]
  have hL : 0 ≤ 12 * t^3 - 20 * t^2 + 128 * t := by
    nlinarith [sq_nonneg (t - 9)]
  have hB : 0 ≤ 4 * t^3 - 11 * t - 1 := by
    nlinarith [sq_nonneg (t - 9), sq_nonneg t]
  have ht_sub_nonneg : 0 ≤ t - 9 := by
    linarith
  have hq_sub_nonneg : 0 ≤ q - 3 := by
    linarith
  have hq_add_nonneg : 0 ≤ q + 3 := by
    linarith
  have hinner_nonneg :
      0 ≤ (3 * t^2 - 10 * t + 3) * (q + 3) + (12 * t^3 - 20 * t^2 + 128 * t) := by
    exact add_nonneg (mul_nonneg hC hq_add_nonneg) hL
  have hbase_nonneg : 0 ≤ 3 * (t - 9) * (4 * t^3 - 11 * t - 1) := by
    have hthree_nonneg : 0 ≤ (3 : ℝ) := by norm_num
    nlinarith [mul_nonneg hthree_nonneg (mul_nonneg ht_sub_nonneg hB)]
  have htail_nonneg :
      0 ≤ (q - 3) *
        ((3 * t^2 - 10 * t + 3) * (q + 3) + (12 * t^3 - 20 * t^2 + 128 * t)) := by
    exact mul_nonneg hq_sub_nonneg hinner_nonneg
  have hdecomp :
      3 * (2 * t^2 + t * q + q)^2 - 16 * t * (9 * t^2 + 2 * t * q + q^2 - 8 * q)
        =
      3 * (t - 9) * (4 * t^3 - 11 * t - 1) +
        (q - 3) *
          ((3 * t^2 - 10 * t + 3) * (q + 3) + (12 * t^3 - 20 * t^2 + 128 * t)) := by
    ring
  rw [hdecomp]
  exact add_nonneg hbase_nonneg htail_nonneg

lemma pair_sq_expand_P13 (a b c s q r : ℝ)
    (hs : s = a + b + c) (hq : q = a * b + a * c + b * c) (hr : r = a * b * c) :
    (s + b)^2 * (s + c)^2 + (s + a)^2 * (s + c)^2 + (s + a)^2 * (s + b)^2
      = 9 * s^4 + 2 * s^2 * q + q^2 - 8 * s * r := by
  subst s
  subst q
  subst r
  ring

lemma prod_sq_expand_P13 (a b c s q r : ℝ)
    (hs : s = a + b + c) (hq : q = a * b + a * c + b * c) (hr : r = a * b * c) :
    (s + a)^2 * (s + b)^2 * (s + c)^2 = (2 * s^3 + s * q + r)^2 := by
  subst s
  subst q
  subst r
  ring

lemma pair_sq_clear_from_sr_P13 (s q r : ℝ) (hsr : s * r = q) :
    9 * s^4 + 2 * s^2 * q + q^2 - 8 * s * r = 9 * s^4 + 2 * s^2 * q + q^2 - 8 * q := by
  nlinarith [hsr]

lemma prod_sq_scaled_clear_from_sr_P13 (s q r : ℝ) (hsr : s * r = q) :
    s^2 * (2 * s^3 + s * q + r)^2 = (2 * s^4 + s^2 * q + q)^2 := by
  have hlin : s * (2 * s^3 + s * q + r) = 2 * s^4 + s^2 * q + q := by
    nlinarith [hsr]
  calc
    s^2 * (2 * s^3 + s * q + r)^2 = (s * (2 * s^3 + s * q + r))^2 := by ring
    _ = (2 * s^4 + s^2 * q + q)^2 := by rw [hlin]

lemma scaled_target_from_poly_P13 (s q A B t : ℝ)
    (ht : t = s^2)
    (hA : A = 9 * s^4 + 2 * s^2 * q + q^2 - 8 * q)
    (hB : s^2 * B = (2 * s^4 + s^2 * q + q)^2)
    (hpoly : 0 ≤ 3 * (2 * t^2 + t * q + q)^2 - 16 * t * (9 * t^2 + 2 * t * q + q^2 - 8 * q)) :
    16 * (s^2 * A) ≤ 3 * (s^2 * B) := by
  subst t
  rw [hA, hB]
  nlinarith

lemma cancel_pos_factor_P13 {u A B : ℝ} (hu : 0 < u) (h : 16 * (u * A) ≤ 3 * (u * B)) :
    16 * A ≤ 3 * B := by
  nlinarith

theorem P13 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : 1/a + 1/b + 1/c = a + b + c) : (2*a + b + c)^(-2:ℝ) + (a + 2*b + c)^(-2:ℝ) + (a + b + 2*c)^(-2:ℝ) ≤ 3 / 16 := by
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hsum_pos : 0 < a + b + c := by
    nlinarith
  have hden₁_pos : 0 < 2 * a + b + c := by
    nlinarith
  have hden₂_pos : 0 < a + 2 * b + c := by
    nlinarith
  have hden₃_pos : 0 < a + b + 2 * c := by
    nlinarith
  have hden₁_ne : 2 * a + b + c ≠ 0 := ne_of_gt hden₁_pos
  have hden₂_ne : a + 2 * b + c ≠ 0 := ne_of_gt hden₂_pos
  have hden₃_ne : a + b + 2 * c ≠ 0 := ne_of_gt hden₃_pos
  have habc_pos : 0 < a * b * c := by
    positivity
  have habc_ne : a * b * c ≠ 0 := ne_of_gt habc_pos
  have h_clear : a * b + a * c + b * c = a * b * c * (a + b + c) := by
    field_simp [ha_ne, hb_ne, hc_ne] at h
    nlinarith [h]
  have h_recip_sq :
      (2*a + b + c)^(-2:ℝ) + (a + 2*b + c)^(-2:ℝ) + (a + b + 2*c)^(-2:ℝ)
        =
      1 / (2*a + b + c)^2 + 1 / (a + 2*b + c)^2 + 1 / (a + b + 2*c)^2 := by
    rw [rpow_neg_two_eq_one_div_sq hden₁_pos,
      rpow_neg_two_eq_one_div_sq hden₂_pos,
      rpow_neg_two_eq_one_div_sq hden₃_pos]
  let s : ℝ := a + b + c
  have hs_pos : 0 < s := by
    dsimp [s]
    nlinarith
  have h_clear_s : a * b + a * c + b * c = a * b * c * s := by
    simpa [s] using h_clear
  have hden₁_shift : 2 * a + b + c = s + a := by
    dsimp [s]
    ring
  have hden₂_shift : a + 2 * b + c = s + b := by
    dsimp [s]
    ring
  have hden₃_shift : a + b + 2 * c = s + c := by
    dsimp [s]
    ring
  have hsa_pos : 0 < s + a := by
    rw [← hden₁_shift]
    exact hden₁_pos
  have hsb_pos : 0 < s + b := by
    rw [← hden₂_shift]
    exact hden₂_pos
  have hsc_pos : 0 < s + c := by
    rw [← hden₃_shift]
    exact hden₃_pos
  have hsa_sq_ne : (s + a)^2 ≠ 0 := by
    exact pow_ne_zero 2 (ne_of_gt hsa_pos)
  have hsb_sq_ne : (s + b)^2 ≠ 0 := by
    exact pow_ne_zero 2 (ne_of_gt hsb_pos)
  have hsc_sq_ne : (s + c)^2 ≠ 0 := by
    exact pow_ne_zero 2 (ne_of_gt hsc_pos)
  have hden_prod_pos : 0 < (s + a)^2 * (s + b)^2 * (s + c)^2 := by
    positivity
  have h_recip_sq_shift :
      (2*a + b + c)^(-2:ℝ) + (a + 2*b + c)^(-2:ℝ) + (a + b + 2*c)^(-2:ℝ)
        =
      1 / (s + a)^2 + 1 / (s + b)^2 + 1 / (s + c)^2 := by
    rw [h_recip_sq]
    rw [hden₁_shift, hden₂_shift, hden₃_shift]
  have h_recip_sq_cleared :
      (1 / (s + a)^2 + 1 / (s + b)^2 + 1 / (s + c)^2 ≤ 3 / 16) ↔
        16 * ((s + b)^2 * (s + c)^2 + (s + a)^2 * (s + c)^2 + (s + a)^2 * (s + b)^2)
          ≤ 3 * ((s + a)^2 * (s + b)^2 * (s + c)^2) := by
    constructor
    · intro hineq
      field_simp [hsa_sq_ne, hsb_sq_ne, hsc_sq_ne] at hineq
      nlinarith
    · intro hineq
      field_simp [hsa_sq_ne, hsb_sq_ne, hsc_sq_ne]
      nlinarith
  have hs_sq_ge_nine : 9 ≤ s^2 := by
    have hq_pos : 0 < a * b + a * c + b * c := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    have h_pair_sq_bound :
        3 * (a * b * c * s) ≤ (a * b + a * c + b * c)^2 := by
      have h1 : 0 ≤ (a * b - a * c)^2 := sq_nonneg (a * b - a * c)
      have h2 : 0 ≤ (a * b - b * c)^2 := sq_nonneg (a * b - b * c)
      have h3 : 0 ≤ (a * c - b * c)^2 := sq_nonneg (a * c - b * c)
      nlinarith only [h1, h2, h3]
    have hq_ge_three : 3 ≤ a * b + a * c + b * c := by
      nlinarith only [h_pair_sq_bound, h_clear_s, hq_pos]
    have hs_sq_bound : 3 * (a * b + a * c + b * c) ≤ s^2 := by
      have h1 : 0 ≤ (a - b)^2 := sq_nonneg (a - b)
      have h2 : 0 ≤ (a - c)^2 := sq_nonneg (a - c)
      have h3 : 0 ≤ (b - c)^2 := sq_nonneg (b - c)
      dsimp [s]
      nlinarith only [h1, h2, h3]
    nlinarith only [hq_ge_three, hs_sq_bound]
  have hq_pos_global : 0 < a * b + a * c + b * c := by
    have hab_pos : 0 < a * b := mul_pos ha hb
    have hac_pos : 0 < a * c := mul_pos ha hc
    have hbc_pos : 0 < b * c := mul_pos hb hc
    linarith
  have h_pair_sq_bound_global :
      3 * (a * b * c * s) ≤ (a * b + a * c + b * c)^2 := by
    have h1 : 0 ≤ (a * b - a * c)^2 := sq_nonneg (a * b - a * c)
    have h2 : 0 ≤ (a * b - b * c)^2 := sq_nonneg (a * b - b * c)
    have h3 : 0 ≤ (a * c - b * c)^2 := sq_nonneg (a * c - b * c)
    nlinarith only [h1, h2, h3]
  have hq_ge_three_global : 3 ≤ a * b + a * c + b * c := by
    nlinarith only [h_pair_sq_bound_global, h_clear_s, hq_pos_global]
  have habc_s_ge_three : 3 ≤ a * b * c * s := by
    nlinarith only [hq_ge_three_global, h_clear_s]
  have h_cleared_key :
      16 * ((s + b)^2 * (s + c)^2 + (s + a)^2 * (s + c)^2 + (s + a)^2 * (s + b)^2)
        ≤ 3 * ((s + a)^2 * (s + b)^2 * (s + c)^2) := by
    let q : ℝ := a * b + a * c + b * c
    let r : ℝ := a * b * c
    let t : ℝ := s^2
    have hqr : q = r * s := by
      dsimp [q, r]
      exact h_clear_s
    have hsr : s * r = q := by
      rw [hqr]
      ring
    have hs_def : s = a + b + c := rfl
    have hq_def : q = a * b + a * c + b * c := rfl
    have hr_def : r = a * b * c := rfl
    have ht_ge_nine : 9 ≤ t := by
      dsimp [t]
      exact hs_sq_ge_nine
    have hq_ge_three : 3 ≤ q := by
      dsimp [q]
      exact hq_ge_three_global
    have h_shift_pair_sq_clear :
        (s + b)^2 * (s + c)^2 + (s + a)^2 * (s + c)^2 + (s + a)^2 * (s + b)^2
          = 9 * s^4 + 2 * s^2 * q + q^2 - 8 * q := by
      calc
        (s + b)^2 * (s + c)^2 + (s + a)^2 * (s + c)^2 + (s + a)^2 * (s + b)^2
            = 9 * s^4 + 2 * s^2 * q + q^2 - 8 * s * r :=
              pair_sq_expand_P13 a b c s q r hs_def hq_def hr_def
        _ = 9 * s^4 + 2 * s^2 * q + q^2 - 8 * q :=
              pair_sq_clear_from_sr_P13 s q r hsr
    have h_shift_prod_sq_scaled_clear :
        s^2 * ((s + a)^2 * (s + b)^2 * (s + c)^2)
          = (2 * s^4 + s^2 * q + q)^2 := by
      calc
        s^2 * ((s + a)^2 * (s + b)^2 * (s + c)^2)
            = s^2 * (2 * s^3 + s * q + r)^2 := by
              rw [prod_sq_expand_P13 a b c s q r hs_def hq_def hr_def]
        _ = (2 * s^4 + s^2 * q + q)^2 :=
              prod_sq_scaled_clear_from_sr_P13 s q r hsr
    have hpoly_nonneg :
        0 ≤ 3 * (2 * t^2 + t * q + q)^2 - 16 * t * (9 * t^2 + 2 * t * q + q^2 - 8 * q) := by
      exact polynomial_key_for_P13 ht_ge_nine hq_ge_three
    have hs_sq_pos : 0 < s^2 := by
      exact sq_pos_of_pos hs_pos
    have hscaled :
        16 * (s^2 *
          ((s + b)^2 * (s + c)^2 + (s + a)^2 * (s + c)^2 + (s + a)^2 * (s + b)^2))
          ≤ 3 * (s^2 * ((s + a)^2 * (s + b)^2 * (s + c)^2)) := by
      exact scaled_target_from_poly_P13 s q
        ((s + b)^2 * (s + c)^2 + (s + a)^2 * (s + c)^2 + (s + a)^2 * (s + b)^2)
        ((s + a)^2 * (s + b)^2 * (s + c)^2) t rfl
        h_shift_pair_sq_clear h_shift_prod_sq_scaled_clear hpoly_nonneg
    exact cancel_pos_factor_P13 hs_sq_pos hscaled
  rw [h_recip_sq_shift]
  exact h_recip_sq_cleared.mpr (by
    exact h_cleared_key)
