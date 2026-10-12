import Mathlib

set_option linter.style.header false
set_option maxHeartbeats 800000

noncomputable section

def atn2 (x y : ℝ) : ℝ :=
  Real.arctan (y / x)

def deltaX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6)
  + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6)
  + x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6)
  - x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6

def deltaX4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6
  + x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

def dihX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let dX4 := deltaX4 x1 x2 x3 x4 x5 x6
  let d := deltaX x1 x2 x3 x4 x5 x6
  Real.pi / 2 + atn2 (Real.sqrt (4 * x1 * d)) (-dX4)

def dihY (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  let x1 := y1 * y1
  let x2 := y2 * y2
  let x3 := y3 * y3
  let x4 := y4 * y4
  let x5 := y5 * y5
  let x6 := y6 * y6
  dihX x1 x2 x3 x4 x5 x6

def solY (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  dihY y1 y2 y3 y4 y5 y6
  + dihY y2 y3 y1 y5 y6 y4
  + dihY y3 y1 y2 y6 y4 y5
  - Real.pi

def const1 : ℝ :=
  solY 2 2 2 2 2 2 / Real.pi

def num1 (e1 e2 e3 a2 b2 c2 : ℝ) : ℝ :=
  -4 * ((a2 ^ 2) * e1 + 8 * (b2 - c2) * (e2 - e3)
    - a2 * (16 * e1 + (b2 - 8) * e2 + (c2 - 8) * e3))

private lemma const1_le_one_fifth : const1 ≤ (1 : ℝ) / 5 := by
  have hconst1_closed :
      const1 =
        (3 * (Real.pi / 2 + Real.arctan (-16 / Real.sqrt 2048)) - Real.pi) /
          Real.pi := by
    norm_num [const1, solY, dihY, dihX, atn2, deltaX, deltaX4]
    ring
  have htan_pi_tenth : Real.tan (Real.pi / 10) ≤ (1 : ℝ) / 3 := by
    have hcos_pos : 0 < Real.cos (Real.pi / 10) := by
      exact Real.cos_pos_of_mem_Ioo
        ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    rw [Real.tan_eq_sin_div_cos]
    rw [div_le_iff₀ hcos_pos]
    apply le_of_sq_le_sq
    · have hsin_sq : Real.sin (Real.pi / 10) ^ 2 = (3 - Real.sqrt 5) / 8 := by
        have hcos2 : Real.cos (2 * (Real.pi / 10)) = (1 + Real.sqrt 5) / 4 := by
          convert Real.cos_pi_div_five using 1
          ring_nf
        have hcos_two := Real.cos_two_mul (Real.pi / 10)
        have hsincos :
            Real.sin (Real.pi / 10) ^ 2 = (1 - Real.cos (2 * (Real.pi / 10))) / 2 := by
          nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 10), hcos_two]
        rw [hsincos, hcos2]
        ring
      have hcos_sq : Real.cos (Real.pi / 10) ^ 2 = (5 + Real.sqrt 5) / 8 := by
        have hcos2 : Real.cos (2 * (Real.pi / 10)) = (1 + Real.sqrt 5) / 4 := by
          convert Real.cos_pi_div_five using 1
          ring_nf
        have hcos_two := Real.cos_two_mul (Real.pi / 10)
        have hsincos := Real.sin_sq_add_cos_sq (Real.pi / 10)
        have hcos_sq' :
            Real.cos (Real.pi / 10) ^ 2 =
              (1 + Real.cos (2 * (Real.pi / 10))) / 2 := by
          nlinarith [hsincos, hcos_two]
        rw [hcos_sq', hcos2]
        ring
      have hmul_sq :
          ((1 : ℝ) / 3 * Real.cos (Real.pi / 10)) ^ 2 =
            Real.cos (Real.pi / 10) ^ 2 / 9 := by
        ring
      rw [hmul_sq, hsin_sq, hcos_sq]
      have hsqrt5_sq : (Real.sqrt 5) ^ 2 = (5 : ℝ) := by norm_num
      nlinarith [Real.sqrt_nonneg 5, hsqrt5_sq]
    · positivity
  have hatan_upper_tenth : Real.arctan (-16 / Real.sqrt 2048) ≤ -(Real.pi / 10) := by
    have hthird_le : (1 : ℝ) / 3 ≤ 16 / Real.sqrt 2048 := by
      have hsqrt_pos : 0 < Real.sqrt 2048 := by positivity
      have hsqrt_le : (Real.sqrt 2048 : ℝ) ≤ 48 := by
        have h := Real.sqrt_le_sqrt (show (2048 : ℝ) ≤ 2304 by norm_num)
        norm_num at h
        exact h
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) hsqrt_pos]
      nlinarith
    have harg_le : -16 / Real.sqrt 2048 ≤ Real.tan (-(Real.pi / 10)) := by
      rw [Real.tan_neg]
      have htan_le_sqrt : Real.tan (Real.pi / 10) ≤ 16 / Real.sqrt 2048 :=
        htan_pi_tenth.trans hthird_le
      have hneg : -(16 / Real.sqrt 2048) ≤ -Real.tan (Real.pi / 10) := by
        linarith
      convert hneg using 1
      ring
    have harctan_tan : Real.arctan (Real.tan (-(Real.pi / 10))) = -(Real.pi / 10) := by
      rw [Real.arctan_tan]
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    rw [← harctan_tan]
    exact (Real.arctan_le_arctan_iff).2 harg_le
  rw [hconst1_closed]
  rw [div_le_iff₀ Real.pi_pos]
  nlinarith [Real.pi_pos, hatan_upper_tenth]

lemma pi_mul_const1_div_pi : (Real.pi * const1) / Real.pi = const1 := by
  field_simp [Real.pi_ne_zero]

lemma num1_mul_neg_one_eq
    (e1 e2 e3 a2 b2 c2 : ℝ) :
    num1 e1 e2 e3 a2 b2 c2 * (-1) =
      4 * ((a2 ^ 2) * e1 + 8 * (b2 - c2) * (e2 - e3)
        - a2 * (16 * e1 + (b2 - 8) * e2 + (c2 - 8) * e3)) := by
  unfold num1
  ring

lemma num1_mul_neg_one_lt_zero_iff
    (e1 e2 e3 a2 b2 c2 : ℝ) :
    num1 e1 e2 e3 a2 b2 c2 * (-1) < 0 ↔
      (a2 ^ 2) * e1 + 8 * (b2 - c2) * (e2 - e3)
        - a2 * (16 * e1 + (b2 - 8) * e2 + (c2 - 8) * e3) < 0 := by
  rw [num1_mul_neg_one_eq]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

lemma core_poly_eq_base_plus_offsets
    (e1 e2 e3 a2 b2 c2 : ℝ) :
    (a2 ^ 2) * e1 + 8 * (b2 - c2) * (e2 - e3)
        - a2 * (16 * e1 + (b2 - 8) * e2 + (c2 - 8) * e3) =
      a2 * (a2 - b2 - c2)
        + (e1 - 1) * (a2 * (a2 - 16))
        + (e2 - 1) * (8 * (b2 - c2) - a2 * (b2 - 8))
        + (e3 - 1) * (-8 * (b2 - c2) - a2 * (c2 - 8)) := by
  ring

lemma coeff_offset_lt_sixty
    (a b c : ℝ)
    (ha_lo : 2 / 1.26 * 2 / 1.26 ≤ a)
    (ha_hi : a ≤ 3.01 * 3.01)
    (hb_lo : 2.38 * 2.38 ≤ b)
    (hb_hi : b ≤ 15.53)
    (hc_lo : 2.38 * 2.38 ≤ c) :
    8 * (b - c) - a * (b - 8) < 60 := by
  have hrewrite :
      8 * (b - c) - a * (b - 8) = b * (8 - a) - 8 * c + 8 * a := by
    ring
  by_cases ha_lt_eight : a < 8
  · have hnonneg : 0 ≤ 8 - a := by linarith
    have hb_mul_le : b * (8 - a) ≤ 15.53 * (8 - a) := by
      exact mul_le_mul_of_nonneg_right hb_hi hnonneg
    rw [hrewrite]
    nlinarith only [hb_mul_le, ha_lo, hc_lo]
  · have ha_ge_eight : 8 ≤ a := le_of_not_gt ha_lt_eight
    have hnonpos : 8 - a ≤ 0 := by linarith
    have hb_mul_le : b * (8 - a) ≤ (2.38 * 2.38) * (8 - a) := by
      exact mul_le_mul_of_nonpos_right hb_lo hnonpos
    rw [hrewrite]
    nlinarith only [hb_mul_le, ha_ge_eight, ha_hi, hc_lo]

theorem ineq6843920790 :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      1 ≤ x1 ∧ x1 ≤ 1 + (Real.pi * const1) / Real.pi ∧
      1 ≤ x2 ∧ x2 ≤ 1 + (Real.pi * const1) / Real.pi ∧
      1 ≤ x3 ∧ x3 ≤ 1 + (Real.pi * const1) / Real.pi ∧
      2 / 1.26 * 2 / 1.26 ≤ x4 ∧ x4 ≤ 3.01 * 3.01 ∧
      2.38 * 2.38 ≤ x5 ∧ x5 ≤ 15.53 ∧
      2.38 * 2.38 ≤ x6 ∧ x6 ≤ 15.53 →
        num1 x1 x2 x3 x4 x5 x6 * (-1) < 0 := by
  intro x1 x2 x3 x4 x5 x6 h
  rcases h with
    ⟨hx1_lo, hx1_hi, hx2_lo, hx2_hi, hx3_lo, hx3_hi,
      hx4_lo, hx4_hi, hx5_lo, hx5_hi, hx6_lo, hx6_hi⟩
  have hx1_hi' : x1 ≤ 1 + const1 := by
    simpa [pi_mul_const1_div_pi] using hx1_hi
  have hx2_hi' : x2 ≤ 1 + const1 := by
    simpa [pi_mul_const1_div_pi] using hx2_hi
  have hx3_hi' : x3 ≤ 1 + const1 := by
    simpa [pi_mul_const1_div_pi] using hx3_hi
  have hx1_pos : 0 < x1 := by nlinarith
  have hx2_pos : 0 < x2 := by nlinarith
  have hx3_pos : 0 < x3 := by nlinarith
  have hx4_pos : 0 < x4 := by
    have hbase : (0 : ℝ) < 2 / 1.26 * 2 / 1.26 := by norm_num
    exact lt_of_lt_of_le hbase hx4_lo
  have hx4_gt_two : 2 < x4 := by
    have hbase : (2 : ℝ) < 2 / 1.26 * 2 / 1.26 := by norm_num
    exact lt_of_lt_of_le hbase hx4_lo
  have hx4_lt_ten : x4 < 10 := by
    have hbase : (3.01 * 3.01 : ℝ) < 10 := by norm_num
    exact lt_of_le_of_lt hx4_hi hbase
  have hx5_pos : 0 < x5 := by
    have hbase : (0 : ℝ) < 2.38 * 2.38 := by norm_num
    exact lt_of_lt_of_le hbase hx5_lo
  have hx5_gt_five : 5 < x5 := by
    have hbase : (5 : ℝ) < 2.38 * 2.38 := by norm_num
    exact lt_of_lt_of_le hbase hx5_lo
  have hx5_lt_sixteen : x5 < 16 := by
    have hbase : (15.53 : ℝ) < 16 := by norm_num
    exact lt_of_le_of_lt hx5_hi hbase
  have hx6_pos : 0 < x6 := by
    have hbase : (0 : ℝ) < 2.38 * 2.38 := by norm_num
    exact lt_of_lt_of_le hbase hx6_lo
  have hx6_gt_five : 5 < x6 := by
    have hbase : (5 : ℝ) < 2.38 * 2.38 := by norm_num
    exact lt_of_lt_of_le hbase hx6_lo
  have hx6_lt_sixteen : x6 < 16 := by
    have hbase : (15.53 : ℝ) < 16 := by norm_num
    exact lt_of_le_of_lt hx6_hi hbase
  have hx1_offset_nonneg : 0 ≤ x1 - 1 := by nlinarith
  have hx2_offset_nonneg : 0 ≤ x2 - 1 := by nlinarith
  have hx3_offset_nonneg : 0 ≤ x3 - 1 := by nlinarith
  have hx1_offset_le_const1 : x1 - 1 ≤ const1 := by nlinarith
  have hx2_offset_le_const1 : x2 - 1 ≤ const1 := by nlinarith
  have hx3_offset_le_const1 : x3 - 1 ≤ const1 := by nlinarith
  have hx4_sub_sixteen_neg : x4 - 16 < 0 := by nlinarith
  have hx4_coeff_e1_neg : x4 * (x4 - 16) < 0 :=
    mul_neg_of_pos_of_neg hx4_pos hx4_sub_sixteen_neg
  have hx4_lt_x5_add_x6 : x4 < x5 + x6 := by nlinarith
  have hbase_term_neg : x4 * (x4 - x5 - x6) < 0 := by
    have hdiff : x4 - x5 - x6 < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg hx4_pos hdiff
  have hx5_add_x6_sub_x4_gt_two : 2 < x5 + x6 - x4 := by
    have hnum : (2 : ℝ) < 2.38 * 2.38 + 2.38 * 2.38 - 3.01 * 3.01 := by
      norm_num
    nlinarith
  have hbase_term_lt_neg_four : x4 * (x4 - x5 - x6) < -4 := by
    have hgap_pos : 0 < x5 + x6 - x4 := by nlinarith
    have hprod :
        (2 : ℝ) * 2 < x4 * (x5 + x6 - x4) := by
      exact mul_lt_mul'' hx4_gt_two hx5_add_x6_sub_x4_gt_two (by norm_num) (by norm_num)
    nlinarith
  have hbase_term_lt_neg_twelve : x4 * (x4 - x5 - x6) < -12 := by
    have hx4_gt_five_halves : (5 / 2 : ℝ) < x4 := by
      have hbase : (5 / 2 : ℝ) < 2 / 1.26 * 2 / 1.26 := by norm_num
      exact lt_of_lt_of_le hbase hx4_lo
    have hgap_gt_eleven_fifths : (11 / 5 : ℝ) < x5 + x6 - x4 := by
      have hnum : (11 / 5 : ℝ) <
          2.38 * 2.38 + 2.38 * 2.38 - 3.01 * 3.01 := by
        norm_num
      nlinarith only [hnum, hx5_lo, hx6_lo, hx4_hi]
    have hprod_gt_twelve : (12 : ℝ) < x4 * (x5 + x6 - x4) := by
      by_cases hx4_lt_six : x4 < 6
      · have hsum_gt_fifty_four_fifths : (54 / 5 : ℝ) < x5 + x6 := by
          have hnum : (54 / 5 : ℝ) < 2.38 * 2.38 + 2.38 * 2.38 := by
            norm_num
          nlinarith only [hnum, hx5_lo, hx6_lo]
        have hgap_gt_twenty_four_fifths : (24 / 5 : ℝ) < x5 + x6 - x4 := by
          linarith only [hsum_gt_fifty_four_fifths, hx4_lt_six]
        have hmul :
            (5 / 2 : ℝ) * (24 / 5) < x4 * (x5 + x6 - x4) := by
          exact mul_lt_mul'' hx4_gt_five_halves hgap_gt_twenty_four_fifths
            (by norm_num) (by norm_num)
        calc
          (12 : ℝ) = (5 / 2 : ℝ) * (24 / 5) := by norm_num
          _ < x4 * (x5 + x6 - x4) := hmul
      · have hx4_ge_six : (6 : ℝ) ≤ x4 := by
          exact le_of_not_gt hx4_lt_six
        have hgap_pos : 0 < x5 + x6 - x4 := by
          linarith only [hgap_gt_eleven_fifths]
        have hleft : (12 : ℝ) < 6 * (11 / 5 : ℝ) := by norm_num
        have hstrict : 6 * (11 / 5 : ℝ) < 6 * (x5 + x6 - x4) := by
          exact mul_lt_mul_of_pos_left hgap_gt_eleven_fifths (by norm_num)
        have hle : 6 * (x5 + x6 - x4) ≤ x4 * (x5 + x6 - x4) := by
          exact mul_le_mul_of_nonneg_right hx4_ge_six (le_of_lt hgap_pos)
        linarith only [hleft, hstrict, hle]
    have hneg_eq :
        x4 * (x4 - x5 - x6) = -(x4 * (x5 + x6 - x4)) := by
      ring
    calc
      x4 * (x4 - x5 - x6) = -(x4 * (x5 + x6 - x4)) := hneg_eq
      _ < -12 := by linarith only [hprod_gt_twelve]
  have hbase_term_lt_neg_twenty : x4 * (x4 - x5 - x6) < -20 := by
    let L : ℝ := 2 / 1.26 * 2 / 1.26
    let U : ℝ := 3.01 * 3.01
    let S : ℝ := 2.38 * 2.38 + 2.38 * 2.38
    have hquad_nonneg : 0 ≤ (x4 - L) * (U - x4) := by
      exact mul_nonneg (sub_nonneg.mpr hx4_lo) (sub_nonneg.mpr hx4_hi)
    have hprod_floor : (20 : ℝ) < x4 * (S - x4) := by
      have hright_endpoint : (20 : ℝ) < U * (S - U) := by
        norm_num [U, S]
      have hK_pos : 0 ≤ (L + U - S) := by
        norm_num [L, U, S]
      have hU_sub_nonneg : 0 ≤ U - x4 := by
        exact sub_nonneg.mpr hx4_hi
      have hrest_nonneg :
          0 ≤ (x4 - L) * (U - x4) + (L + U - S) * (U - x4) := by
        exact add_nonneg hquad_nonneg (mul_nonneg hK_pos hU_sub_nonneg)
      have hfloor_eq :
          x4 * (S - x4) =
            U * (S - U)
              + ((x4 - L) * (U - x4) + (L + U - S) * (U - x4)) := by
        ring
      rw [hfloor_eq]
      linarith only [hright_endpoint, hrest_nonneg]
    have hgap_floor_le : x4 * (S - x4) ≤ x4 * (x5 + x6 - x4) := by
      have hS_le_sum : S ≤ x5 + x6 := by
        dsimp [S]
        linarith only [hx5_lo, hx6_lo]
      have hS_le : S - x4 ≤ x5 + x6 - x4 := by
        linarith only [hS_le_sum]
      exact mul_le_mul_of_nonneg_left hS_le (le_of_lt hx4_pos)
    have hprod_gt_twenty : (20 : ℝ) < x4 * (x5 + x6 - x4) := by
      exact lt_of_lt_of_le hprod_floor hgap_floor_le
    have hneg_eq :
        x4 * (x4 - x5 - x6) = -(x4 * (x5 + x6 - x4)) := by
      ring
    calc
      x4 * (x4 - x5 - x6) = -(x4 * (x5 + x6 - x4)) := hneg_eq
      _ < -20 := by linarith only [hprod_gt_twenty]
  have hx1_offset_term_nonpos :
      (x1 - 1) * (x4 * (x4 - 16)) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos hx1_offset_nonneg (le_of_lt hx4_coeff_e1_neg)
  have hbase_plus_x1_offset_lt_neg_four :
      x4 * (x4 - x5 - x6) + (x1 - 1) * (x4 * (x4 - 16)) < -4 := by
    linarith only [hbase_term_lt_neg_four, hx1_offset_term_nonpos]
  have hbase_plus_x1_offset_lt_neg_twelve :
      x4 * (x4 - x5 - x6) + (x1 - 1) * (x4 * (x4 - 16)) < -12 := by
    linarith only [hbase_term_lt_neg_twelve, hx1_offset_term_nonpos]
  have hbase_plus_x1_offset_lt_neg_twenty :
      x4 * (x4 - x5 - x6) + (x1 - 1) * (x4 * (x4 - 16)) < -20 := by
    linarith only [hbase_term_lt_neg_twenty, hx1_offset_term_nonpos]
  have hconst1_nonneg : 0 ≤ const1 :=
    le_trans hx1_offset_nonneg hx1_offset_le_const1
  have hcore_decomp :
      (x4 ^ 2) * x1 + 8 * (x5 - x6) * (x2 - x3)
          - x4 * (16 * x1 + (x5 - 8) * x2 + (x6 - 8) * x3) =
        x4 * (x4 - x5 - x6)
          + (x1 - 1) * (x4 * (x4 - 16))
          + (x2 - 1) * (8 * (x5 - x6) - x4 * (x5 - 8))
          + (x3 - 1) * (-8 * (x5 - x6) - x4 * (x6 - 8)) := by
    simpa using core_poly_eq_base_plus_offsets x1 x2 x3 x4 x5 x6
  have hcoeff_x2_lt_sixty :
      8 * (x5 - x6) - x4 * (x5 - 8) < 60 := by
    exact coeff_offset_lt_sixty x4 x5 x6 hx4_lo hx4_hi hx5_lo hx5_hi hx6_lo
  have hcoeff_x3_lt_sixty :
      -8 * (x5 - x6) - x4 * (x6 - 8) < 60 := by
    have h := coeff_offset_lt_sixty x4 x6 x5 hx4_lo hx4_hi hx6_lo hx6_hi hx5_lo
    nlinarith only [h]
  have hcoeff_x2_add_x3_lt_sixty :
      (8 * (x5 - x6) - x4 * (x5 - 8))
        + (-8 * (x5 - x6) - x4 * (x6 - 8)) < 60 := by
    have hsum_lo : 2.38 * 2.38 + 2.38 * 2.38 ≤ x5 + x6 := by
      exact add_le_add hx5_lo hx6_lo
    have hfactor_le :
        16 - (x5 + x6) ≤ 16 - (2.38 * 2.38 + 2.38 * 2.38) := by
      exact sub_le_sub_left hsum_lo 16
    have hmul_le :
        x4 * (16 - (x5 + x6)) ≤
          x4 * (16 - (2.38 * 2.38 + 2.38 * 2.38)) := by
      exact mul_le_mul_of_nonneg_left hfactor_le (le_of_lt hx4_pos)
    have hmul_lt_sixty :
        x4 * (16 - (2.38 * 2.38 + 2.38 * 2.38)) < 60 := by
      have hfactor_nonneg :
          0 ≤ 16 - (2.38 * 2.38 + 2.38 * 2.38 : ℝ) := by
        norm_num
      have hfactor_lt_five :
          16 - (2.38 * 2.38 + 2.38 * 2.38 : ℝ) < 5 := by
        norm_num
      have hprod_lt :
          x4 * (16 - (2.38 * 2.38 + 2.38 * 2.38)) < (10 : ℝ) * 5 := by
        exact mul_lt_mul'' hx4_lt_ten hfactor_lt_five (le_of_lt hx4_pos) hfactor_nonneg
      exact lt_trans hprod_lt (by norm_num)
    have hsum_eq :
        (8 * (x5 - x6) - x4 * (x5 - 8))
          + (-8 * (x5 - x6) - x4 * (x6 - 8)) =
            x4 * (16 - (x5 + x6)) := by
      ring
    rw [hsum_eq]
    exact lt_of_le_of_lt hmul_le hmul_lt_sixty
  have hx2_offset_term_le_const1_sixty :
      (x2 - 1) * (8 * (x5 - x6) - x4 * (x5 - 8)) ≤ const1 * 60 := by
    have hcoeff_le :
        8 * (x5 - x6) - x4 * (x5 - 8) ≤ 60 :=
      le_of_lt hcoeff_x2_lt_sixty
    have hstep1 :
        (x2 - 1) * (8 * (x5 - x6) - x4 * (x5 - 8)) ≤ (x2 - 1) * 60 := by
      exact mul_le_mul_of_nonneg_left hcoeff_le hx2_offset_nonneg
    have hstep2 : (x2 - 1) * 60 ≤ const1 * 60 := by
      exact mul_le_mul_of_nonneg_right hx2_offset_le_const1 (by norm_num)
    linarith
  have hx3_offset_term_le_const1_sixty :
      (x3 - 1) * (-8 * (x5 - x6) - x4 * (x6 - 8)) ≤ const1 * 60 := by
    have hcoeff_le :
        -8 * (x5 - x6) - x4 * (x6 - 8) ≤ 60 :=
      le_of_lt hcoeff_x3_lt_sixty
    have hstep1 :
        (x3 - 1) * (-8 * (x5 - x6) - x4 * (x6 - 8)) ≤ (x3 - 1) * 60 := by
      exact mul_le_mul_of_nonneg_left hcoeff_le hx3_offset_nonneg
    have hstep2 : (x3 - 1) * 60 ≤ const1 * 60 := by
      exact mul_le_mul_of_nonneg_right hx3_offset_le_const1 (by norm_num)
    linarith
  have htail_offsets_le_const1_sharp :
      (x2 - 1) * (8 * (x5 - x6) - x4 * (x5 - 8))
        + (x3 - 1) * (-8 * (x5 - x6) - x4 * (x6 - 8)) ≤ const1 * 120 := by
    linarith only [hx2_offset_term_le_const1_sixty, hx3_offset_term_le_const1_sixty]
  have htail_offsets_le_const1_sixty :
      (x2 - 1) * (8 * (x5 - x6) - x4 * (x5 - 8))
        + (x3 - 1) * (-8 * (x5 - x6) - x4 * (x6 - 8)) ≤ const1 * 60 := by
    by_cases hcoeff2_nonpos : 8 * (x5 - x6) - x4 * (x5 - 8) ≤ 0
    · have hterm2_nonpos :
          (x2 - 1) * (8 * (x5 - x6) - x4 * (x5 - 8)) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos hx2_offset_nonneg hcoeff2_nonpos
      by_cases hcoeff3_nonpos : -8 * (x5 - x6) - x4 * (x6 - 8) ≤ 0
      · have hterm3_nonpos :
            (x3 - 1) * (-8 * (x5 - x6) - x4 * (x6 - 8)) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos hx3_offset_nonneg hcoeff3_nonpos
        have hconst1_sixty_nonneg : 0 ≤ const1 * 60 := by
          exact mul_nonneg hconst1_nonneg (by norm_num)
        linarith only [hterm2_nonpos, hterm3_nonpos, hconst1_sixty_nonneg]
      · have hcoeff3_nonneg : 0 ≤ -8 * (x5 - x6) - x4 * (x6 - 8) := by
          exact le_of_lt (lt_of_not_ge hcoeff3_nonpos)
        have hterm3_le :
            (x3 - 1) * (-8 * (x5 - x6) - x4 * (x6 - 8)) ≤
              const1 * (-8 * (x5 - x6) - x4 * (x6 - 8)) := by
          exact mul_le_mul_of_nonneg_right hx3_offset_le_const1 hcoeff3_nonneg
        have hconst1_coeff3_le :
            const1 * (-8 * (x5 - x6) - x4 * (x6 - 8)) ≤ const1 * 60 := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hcoeff_x3_lt_sixty) hconst1_nonneg
        linarith only [hterm2_nonpos, hterm3_le, hconst1_coeff3_le]
    · have hcoeff2_nonneg : 0 ≤ 8 * (x5 - x6) - x4 * (x5 - 8) := by
        exact le_of_lt (lt_of_not_ge hcoeff2_nonpos)
      have hterm2_le :
          (x2 - 1) * (8 * (x5 - x6) - x4 * (x5 - 8)) ≤
            const1 * (8 * (x5 - x6) - x4 * (x5 - 8)) := by
        exact mul_le_mul_of_nonneg_right hx2_offset_le_const1 hcoeff2_nonneg
      by_cases hcoeff3_nonpos : -8 * (x5 - x6) - x4 * (x6 - 8) ≤ 0
      · have hterm3_nonpos :
            (x3 - 1) * (-8 * (x5 - x6) - x4 * (x6 - 8)) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos hx3_offset_nonneg hcoeff3_nonpos
        have hconst1_coeff2_le :
            const1 * (8 * (x5 - x6) - x4 * (x5 - 8)) ≤ const1 * 60 := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hcoeff_x2_lt_sixty) hconst1_nonneg
        linarith only [hterm2_le, hterm3_nonpos, hconst1_coeff2_le]
      · have hcoeff3_nonneg : 0 ≤ -8 * (x5 - x6) - x4 * (x6 - 8) := by
          exact le_of_lt (lt_of_not_ge hcoeff3_nonpos)
        have hterm3_le :
            (x3 - 1) * (-8 * (x5 - x6) - x4 * (x6 - 8)) ≤
              const1 * (-8 * (x5 - x6) - x4 * (x6 - 8)) := by
          exact mul_le_mul_of_nonneg_right hx3_offset_le_const1 hcoeff3_nonneg
        have hconst1_coeff_sum_le :
            const1 * ((8 * (x5 - x6) - x4 * (x5 - 8))
              + (-8 * (x5 - x6) - x4 * (x6 - 8))) ≤ const1 * 60 := by
          exact mul_le_mul_of_nonneg_left (le_of_lt hcoeff_x2_add_x3_lt_sixty) hconst1_nonneg
        have hconst1_add :
            const1 * (8 * (x5 - x6) - x4 * (x5 - 8))
              + const1 * (-8 * (x5 - x6) - x4 * (x6 - 8)) =
                const1 * ((8 * (x5 - x6) - x4 * (x5 - 8))
                  + (-8 * (x5 - x6) - x4 * (x6 - 8))) := by
          ring
        linarith only [hterm2_le, hterm3_le, hconst1_coeff_sum_le, hconst1_add]
  have hcore_lt_neg_twelve_plus_const1_sharp :
      (x4 ^ 2) * x1 + 8 * (x5 - x6) * (x2 - x3)
          - x4 * (16 * x1 + (x5 - 8) * x2 + (x6 - 8) * x3)
        < -12 + const1 * 120 := by
    rw [hcore_decomp]
    linarith only [hbase_plus_x1_offset_lt_neg_twelve, htail_offsets_le_const1_sharp]
  have hcore_lt_neg_twenty_plus_const1_sixty :
      (x4 ^ 2) * x1 + 8 * (x5 - x6) * (x2 - x3)
          - x4 * (16 * x1 + (x5 - 8) * x2 + (x6 - 8) * x3)
        < -20 + const1 * 60 := by
    rw [hcore_decomp]
    linarith only [hbase_plus_x1_offset_lt_neg_twenty, htail_offsets_le_const1_sixty]
  rw [num1_mul_neg_one_lt_zero_iff]
  have hcore_lt_of_const1_lt_one_third :
      const1 < 1 / 3 →
        (x4 ^ 2) * x1 + 8 * (x5 - x6) * (x2 - x3)
            - x4 * (16 * x1 + (x5 - 8) * x2 + (x6 - 8) * x3) < 0 := by
    intro hconst1_lt_one_third
    have hconst1_sixty_lt_twenty : const1 * 60 < 20 := by
      nlinarith only [hconst1_lt_one_third]
    linarith only [hcore_lt_neg_twenty_plus_const1_sixty, hconst1_sixty_lt_twenty]
  have hconst1_lt_one_third : const1 < 1 / 3 := by
    nlinarith [const1_le_one_fifth]
  exact hcore_lt_of_const1_lt_one_third hconst1_lt_one_third
