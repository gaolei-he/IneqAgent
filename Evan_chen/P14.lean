import Mathlib

set_option maxHeartbeats 1000000

lemma P14_SX_poly_nonneg (S X : ℝ) (hS : 3 ≤ S) (hX : 3 ≤ X) :
    0 ≤ 12 * S ^ 8 + 12 * S ^ 6 * X - 144 * S ^ 6
      + 3 * S ^ 4 * X ^ 2 - 20 * S ^ 4 * X
      - 10 * S ^ 2 * X ^ 2 + 128 * S ^ 2 * X + 3 * X ^ 2 := by
  have hlast : 0 ≤ 4 * S ^ 6 - 11 * S ^ 2 - 1 := by
    nlinarith [sq_nonneg (S ^ 2 - 9)]
  have hsminus : 0 ≤ S - 3 := by
    nlinarith
  have hsplus : 0 ≤ S + 3 := by
    nlinarith
  have hcoef : 0 ≤ 3 * S ^ 4 - 10 * S ^ 2 + 3 := by
    nlinarith [sq_nonneg (S ^ 2 - 9)]
  have hbase : 0 ≤ 2 * (6 * S ^ 6 - S ^ 4 + 34 * S ^ 2 + 9) := by
    nlinarith [sq_nonneg (S ^ 2 - 9)]
  have hN3 : 0 ≤ 3 * (S - 3) * (S + 3) * (4 * S ^ 6 - 11 * S ^ 2 - 1) := by
    have hprod : 0 ≤ (S - 3) * (S + 3) * (4 * S ^ 6 - 11 * S ^ 2 - 1) := by
      exact mul_nonneg (mul_nonneg hsminus hsplus) hlast
    nlinarith [hprod]
  have hxsub : 0 ≤ X - 3 := by
    nlinarith
  have hD :
      0 ≤ 12 * S ^ 6 + 3 * S ^ 4 * X - 11 * S ^ 4
        - 10 * S ^ 2 * X + 98 * S ^ 2 + 3 * X + 9 := by
    nlinarith [mul_nonneg hcoef hxsub, hbase]
  have hterm :
      0 ≤ (X - 3) * (12 * S ^ 6 + 3 * S ^ 4 * X - 11 * S ^ 4
        - 10 * S ^ 2 * X + 98 * S ^ 2 + 3 * X + 9) := by
    positivity
  nlinarith [hN3, hterm]

theorem P14 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1 / a + 1 / b + 1 / c) : 1 / (2 * a + b + c) ^ 2 + 1 / (a + 2 * b + c) ^ 2 + 1 / (a + b + 2 * c) ^ 2 ≤ 3 / 16 := by
  let s : ℝ := a + b + c
  have hs_pos : 0 < s := by
    dsimp [s]
    linarith
  have hsum_pos : 0 < a + b + c := by
    nlinarith [ha, hb, hc]
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have ha_div_s_pos : 0 < a / s := div_pos ha hs_pos
  have hb_div_s_pos : 0 < b / s := div_pos hb hs_pos
  have hc_div_s_pos : 0 < c / s := div_pos hc hs_pos
  have hnormalized_sum : a / s + b / s + c / s = 1 := by
    field_simp [hs_ne]
    dsimp [s]
  have hden_a_eq : 2 * a + b + c = s + a := by
    dsimp [s]
    ring
  have hden_b_eq : a + 2 * b + c = s + b := by
    dsimp [s]
    ring
  have hden_c_eq : a + b + 2 * c = s + c := by
    dsimp [s]
    ring
  have hden_a_pos : 0 < 2 * a + b + c := by
    rw [hden_a_eq]
    linarith
  have hden_b_pos : 0 < a + 2 * b + c := by
    rw [hden_b_eq]
    linarith
  have hden_c_pos : 0 < a + b + 2 * c := by
    rw [hden_c_eq]
    linarith
  have hden_a_ne : 2 * a + b + c ≠ 0 := ne_of_gt hden_a_pos
  have hden_b_ne : a + 2 * b + c ≠ 0 := ne_of_gt hden_b_pos
  have hden_c_ne : a + b + 2 * c ≠ 0 := ne_of_gt hden_c_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hclear : b * c + a * c + a * b = a * b * c * (a + b + c) := by
    have hlocal := h.symm
    field_simp [ha_ne, hb_ne, hc_ne] at hlocal
    nlinarith [hlocal]
  have habc_pos : 0 < a * b * c := by
    positivity
  have hsum_ge_three : 3 ≤ a + b + c := by
    have hschur : 9 * (a * b * c) ≤ (a + b + c) * (a * b + a * c + b * c) := by
      have hsq_nonneg :
          0 ≤ a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 := by
        positivity
      nlinarith [hsq_nonneg]
    have hclear' : a * b + a * c + b * c = a * b * c * (a + b + c) := by
      nlinarith [hclear]
    have hmul_sq : a * b * c * 9 ≤ a * b * c * (a + b + c) ^ 2 := by
      nlinarith [hschur, hclear']
    have hsum_sq_ge : 9 ≤ (a + b + c) ^ 2 := by
      exact (mul_le_mul_iff_left₀ habc_pos).mp
        (by simpa [mul_assoc, mul_comm, mul_left_comm] using hmul_sq)
    nlinarith [hsum_sq_ge, hsum_pos, sq_nonneg (a + b + c - 3)]
  have hsum_mul_abc_ge_three : 3 ≤ (a + b + c) * (a * b * c) := by
    have hq_sq_ge :
        3 * (a * b * c * (a + b + c)) ≤ (a * b + a * c + b * c) ^ 2 := by
      have hsq_ab_ac : 0 ≤ (a * b - a * c) ^ 2 := sq_nonneg _
      have hsq_ab_bc : 0 ≤ (a * b - b * c) ^ 2 := sq_nonneg _
      have hsq_ac_bc : 0 ≤ (a * c - b * c) ^ 2 := sq_nonneg _
      nlinarith
    have hclear' : a * b + a * c + b * c = a * b * c * (a + b + c) := by
      nlinarith [hclear]
    have hx_sq :
        3 * ((a + b + c) * (a * b * c)) ≤ ((a + b + c) * (a * b * c)) ^ 2 := by
      nlinarith [hq_sq_ge, hclear']
    have hx_pos : 0 < (a + b + c) * (a * b * c) := by
      positivity
    exact le_of_mul_le_mul_right
      (by simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hx_sq) hx_pos
  have hpoly_reduced :
      0 ≤ 12 * (a + b + c) ^ 6
        + 12 * (a + b + c) ^ 5 * (a * b * c)
        + 3 * (a + b + c) ^ 4 * (a * b * c) ^ 2
        - 144 * (a + b + c) ^ 4
        - 20 * (a + b + c) ^ 3 * (a * b * c)
        - 10 * (a + b + c) ^ 2 * (a * b * c) ^ 2
        + 128 * (a + b + c) * (a * b * c)
        + 3 * (a * b * c) ^ 2 := by
    have hN := P14_SX_poly_nonneg (a + b + c) ((a + b + c) * (a * b * c))
      hsum_ge_three hsum_mul_abc_ge_three
    have hscaled :
        0 ≤ (a + b + c) ^ 2 *
          (12 * (a + b + c) ^ 6
            + 12 * (a + b + c) ^ 5 * (a * b * c)
            + 3 * (a + b + c) ^ 4 * (a * b * c) ^ 2
            - 144 * (a + b + c) ^ 4
            - 20 * (a + b + c) ^ 3 * (a * b * c)
            - 10 * (a + b + c) ^ 2 * (a * b * c) ^ 2
            + 128 * (a + b + c) * (a * b * c)
            + 3 * (a * b * c) ^ 2) := by
      have hscaled_eq :
          (a + b + c) ^ 2 *
            (12 * (a + b + c) ^ 6
              + 12 * (a + b + c) ^ 5 * (a * b * c)
              + 3 * (a + b + c) ^ 4 * (a * b * c) ^ 2
              - 144 * (a + b + c) ^ 4
              - 20 * (a + b + c) ^ 3 * (a * b * c)
              - 10 * (a + b + c) ^ 2 * (a * b * c) ^ 2
              + 128 * (a + b + c) * (a * b * c)
              + 3 * (a * b * c) ^ 2)
          = 12 * (a + b + c) ^ 8
              + 12 * (a + b + c) ^ 6 * ((a + b + c) * (a * b * c))
              - 144 * (a + b + c) ^ 6
              + 3 * (a + b + c) ^ 4 * ((a + b + c) * (a * b * c)) ^ 2
              - 20 * (a + b + c) ^ 4 * ((a + b + c) * (a * b * c))
              - 10 * (a + b + c) ^ 2 * ((a + b + c) * (a * b * c)) ^ 2
              + 128 * (a + b + c) ^ 2 * ((a + b + c) * (a * b * c))
              + 3 * ((a + b + c) * (a * b * c)) ^ 2 := by
        ring
      rw [hscaled_eq]
      exact hN
    have hsum_sq_pos : 0 < (a + b + c) ^ 2 := by
      positivity
    exact (mul_nonneg_iff_of_pos_left hsum_sq_pos).mp hscaled
  have hpairs_eq : a * b + a * c + b * c = (a + b + c) * (a * b * c) := by
    calc
      a * b + a * c + b * c = b * c + a * c + a * b := by ring
      _ = a * b * c * (a + b + c) := by
        exact hclear
      _ = (a + b + c) * (a * b * c) := by ring
  have hden_poly_nonneg :
      0 ≤ 3 * ((2 * a + b + c) ^ 2
          * (a + 2 * b + c) ^ 2
          * (a + b + 2 * c) ^ 2)
        - 16 * ((a + 2 * b + c) ^ 2 * (a + b + 2 * c) ^ 2
          + (2 * a + b + c) ^ 2 * (a + b + 2 * c) ^ 2
          + (2 * a + b + c) ^ 2 * (a + 2 * b + c) ^ 2) := by
    have hden_poly_eq :
        3 * ((2 * a + b + c) ^ 2
            * (a + 2 * b + c) ^ 2
            * (a + b + 2 * c) ^ 2)
          - 16 * ((a + 2 * b + c) ^ 2 * (a + b + 2 * c) ^ 2
            + (2 * a + b + c) ^ 2 * (a + b + 2 * c) ^ 2
            + (2 * a + b + c) ^ 2 * (a + 2 * b + c) ^ 2)
        = 12 * (a + b + c) ^ 6
          + 12 * (a + b + c) ^ 5 * (a * b * c)
          + 3 * (a + b + c) ^ 4 * (a * b * c) ^ 2
          - 144 * (a + b + c) ^ 4
          - 20 * (a + b + c) ^ 3 * (a * b * c)
          - 10 * (a + b + c) ^ 2 * (a * b * c) ^ 2
          + 128 * (a + b + c) * (a * b * c)
          + 3 * (a * b * c) ^ 2 := by
      calc
        3 * ((2 * a + b + c) ^ 2
            * (a + 2 * b + c) ^ 2
            * (a + b + 2 * c) ^ 2)
          - 16 * ((a + 2 * b + c) ^ 2 * (a + b + 2 * c) ^ 2
            + (2 * a + b + c) ^ 2 * (a + b + 2 * c) ^ 2
            + (2 * a + b + c) ^ 2 * (a + 2 * b + c) ^ 2)
          = 12 * (a + b + c) ^ 6
          + 12 * (a + b + c) ^ 4 * (a * b + a * c + b * c)
          - 144 * (a + b + c) ^ 4
          + 12 * (a + b + c) ^ 3 * (a * b * c)
          + 3 * (a + b + c) ^ 2 * (a * b + a * c + b * c) ^ 2
          - 32 * (a + b + c) ^ 2 * (a * b + a * c + b * c)
          + 6 * (a + b + c) * (a * b + a * c + b * c) * (a * b * c)
          + 128 * (a + b + c) * (a * b * c)
              - 16 * (a * b + a * c + b * c) ^ 2
              + 3 * (a * b * c) ^ 2 := by
            ring
        _ = 12 * (a + b + c) ^ 6
          + 12 * (a + b + c) ^ 5 * (a * b * c)
          + 3 * (a + b + c) ^ 4 * (a * b * c) ^ 2
          - 144 * (a + b + c) ^ 4
          - 20 * (a + b + c) ^ 3 * (a * b * c)
          - 10 * (a + b + c) ^ 2 * (a * b * c) ^ 2
          + 128 * (a + b + c) * (a * b * c)
          + 3 * (a * b * c) ^ 2 := by
            rw [hpairs_eq]
            ring
    rw [hden_poly_eq]
    exact hpoly_reduced
  have hnorm_from_clear :
      16 * ((a + 2 * b + c) ^ 2 * (a + b + 2 * c) ^ 2
          + (2 * a + b + c) ^ 2 * (a + b + 2 * c) ^ 2
          + (2 * a + b + c) ^ 2 * (a + 2 * b + c) ^ 2)
        ≤ 3 * ((2 * a + b + c) ^ 2
          * (a + 2 * b + c) ^ 2
          * (a + b + 2 * c) ^ 2) →
      1 / (2 * a + b + c) ^ 2
        + 1 / (a + 2 * b + c) ^ 2
        + 1 / (a + b + 2 * c) ^ 2 ≤ 3 / 16 := by
    intro hpoly
    field_simp [hden_a_ne, hden_b_ne, hden_c_ne]
    nlinarith [hpoly]
  apply hnorm_from_clear
  exact sub_nonneg.mp hden_poly_nonneg
