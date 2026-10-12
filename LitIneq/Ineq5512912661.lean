import Mathlib

set_option linter.style.header false
set_option maxHeartbeats 0

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

private lemma x2_perturbation_factor_bound {x4 x5 x6 : ℝ}
    (hx4u : x4 ≤ (9.0601 : ℝ)) (hx5l : (4 : ℝ) ≤ x5)
    (hx5u : x5 ≤ (6.3504 : ℝ)) (hx6l : (6.25 : ℝ) ≤ x6) :
    (8 - x4) * x5 + 8 * x4 - 8 * x6 ≤ 18.2404 := by
  have hb_nonpos : x5 - 8 ≤ 0 := by nlinarith
  have hx4_shift_upper : x4 - 8 ≤ 1.0601 := by nlinarith
  have hprod_lower : -4.2404 ≤ (x4 - 8) * (x5 - 8) := by
    have hmul : (1.0601 : ℝ) * (x5 - 8) ≤ (x4 - 8) * (x5 - 8) := by
      exact mul_le_mul_of_nonpos_right hx4_shift_upper hb_nonpos
    have hconst : -4.2404 ≤ (1.0601 : ℝ) * (x5 - 8) := by nlinarith
    linarith
  nlinarith [hprod_lower, hx6l]

private lemma core_box_bound {x1 x2 x3 x4 x5 x6 : ℝ}
    (hx1l : 1 ≤ x1)
    (hx2l : 1 ≤ x2) (hx2u : x2 ≤ (6 : ℝ) / 5)
    (hx3l : 1 ≤ x3) (hx3u : x3 ≤ (6 : ℝ) / 5)
    (hx4l : (5.6644 : ℝ) ≤ x4) (hx4u : x4 ≤ (9.0601 : ℝ))
    (hx5l : (4 : ℝ) ≤ x5) (hx5u : x5 ≤ (6.3504 : ℝ))
    (hx6l : (6.25 : ℝ) ≤ x6) :
    (x4 ^ 2) * x1 + 8 * (x5 - x6) * (x2 - x3)
        - x4 * (16 * x1 + (x5 - 8) * x2 + (x6 - 8) * x3) < 0 := by
  have hu1_nonneg : 0 ≤ x1 - 1 := by linarith
  have hu2_nonneg : 0 ≤ x2 - 1 := by linarith
  have hu2_upper : x2 - 1 ≤ (1 : ℝ) / 5 := by linarith
  have hu3_nonneg : 0 ≤ x3 - 1 := by linarith
  have hu3_upper : x3 - 1 ≤ (1 : ℝ) / 5 := by linarith
  have hf1_nonpos : x4 * (x4 - 16) ≤ 0 := by nlinarith
  have h_u1 : (x1 - 1) * (x4 * (x4 - 16)) ≤ 0 := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hu1_nonneg hf1_nonpos]
  have hf2_upper : (8 - x4) * x5 + 8 * x4 - 8 * x6 ≤ 18.2404 := by
    exact x2_perturbation_factor_bound hx4u hx5l hx5u hx6l
  have h_u2 : (x2 - 1) * ((8 - x4) * x5 + 8 * x4 - 8 * x6) ≤
      (1 / 5) * (18.2404 : ℝ) := by
    by_cases hpos : 0 ≤ (8 - x4) * x5 + 8 * x4 - 8 * x6
    · exact mul_le_mul hu2_upper hf2_upper hpos (by norm_num)
    · have hnonpos : (8 - x4) * x5 + 8 * x4 - 8 * x6 ≤ 0 := le_of_not_ge hpos
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hu2_nonneg hnonpos]
  have h_base_u3 : x4 * (x4 - x5 - x6) + (1 / 5) * (18.2404 : ℝ) +
      (x3 - 1) * ((8 - x4) * x6 + 8 * x4 - 8 * x5) ≤ -0.36149799 := by
    by_cases hpos : 0 ≤ (8 - x4) * x6 + 8 * x4 - 8 * x5
    · have h_u3 : (x3 - 1) * ((8 - x4) * x6 + 8 * x4 - 8 * x5) ≤
          (1 / 5) * ((8 - x4) * x6 + 8 * x4 - 8 * x5) := by
        exact mul_le_mul hu3_upper
          (le_refl ((8 - x4) * x6 + 8 * x4 - 8 * x5)) hpos (by norm_num)
      have hq : x4 * (x4 - x5 - x6) + (1 / 5) * (18.2404 : ℝ) +
          (1 / 5) * ((8 - x4) * x6 + 8 * x4 - 8 * x5) ≤ -0.36149799 := by
        have hcoef5 : 0 ≤ x4 + (8 : ℝ) / 5 := by nlinarith
        have hcoef6 : 0 ≤ (6 : ℝ) / 5 * x4 - (8 : ℝ) / 5 := by nlinarith
        have h5 : -(x4 + (8 : ℝ) / 5) * x5 ≤ -(x4 + (8 : ℝ) / 5) * 4 := by
          nlinarith [mul_le_mul_of_nonneg_left hx5l hcoef5]
        have h6 : -((6 : ℝ) / 5 * x4 - (8 : ℝ) / 5) * x6 ≤
            -((6 : ℝ) / 5 * x4 - (8 : ℝ) / 5) * 6.25 := by
          nlinarith [mul_le_mul_of_nonneg_left hx6l hcoef6]
        have hmono : x4 ^ 2 - (99 : ℝ) / 10 * x4 + 7.24808 ≤ -0.36149799 := by
          have hleft : x4 - 9.0601 ≤ 0 := by nlinarith
          have hright : 0 ≤ x4 - 0.8399 := by nlinarith
          nlinarith [mul_nonpos_of_nonpos_of_nonneg hleft hright]
        nlinarith [h5, h6, hmono]
      nlinarith
    · have hnonpos : (8 - x4) * x6 + 8 * x4 - 8 * x5 ≤ 0 := le_of_not_ge hpos
      have h_u3 : (x3 - 1) * ((8 - x4) * x6 + 8 * x4 - 8 * x5) ≤ 0 := by
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hu3_nonneg hnonpos]
      have hbase : x4 * (x4 - x5 - x6) + (1 / 5) * (18.2404 : ℝ) ≤ -7.13253299 := by
        have hcoef : 0 ≤ x4 := by nlinarith
        have hsum : (10.25 : ℝ) ≤ x5 + x6 := by nlinarith
        have hterm : -x4 * (x5 + x6) ≤ -x4 * 10.25 := by
          nlinarith [mul_le_mul_of_nonneg_left hsum hcoef]
        have hmono : x4 ^ 2 - 10.25 * x4 + (1 / 5) * (18.2404 : ℝ) ≤ -7.13253299 := by
          have hleft : x4 - 9.0601 ≤ 0 := by nlinarith
          have hright : 0 ≤ x4 - 1.1899 := by nlinarith
          nlinarith [mul_nonpos_of_nonpos_of_nonneg hleft hright]
        nlinarith [hterm, hmono]
      nlinarith [h_u3, hbase]
  have hdecomp :
      (x4 ^ 2) * x1 + 8 * (x5 - x6) * (x2 - x3)
          - x4 * (16 * x1 + (x5 - 8) * x2 + (x6 - 8) * x3) =
        x4 * (x4 - x5 - x6) + (x1 - 1) * (x4 * (x4 - 16)) +
          (x2 - 1) * ((8 - x4) * x5 + 8 * x4 - 8 * x6) +
          (x3 - 1) * ((8 - x4) * x6 + 8 * x4 - 8 * x5) := by
    ring
  rw [hdecomp]
  nlinarith [h_u1, h_u2, h_base_u3]

theorem ineq5512912661 :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      1 ≤ x1 ∧ x1 ≤ 1 + (Real.pi * const1) / Real.pi ∧
      1 ≤ x2 ∧ x2 ≤ 1 + (Real.pi * const1) / Real.pi ∧
      1 ≤ x3 ∧ x3 ≤ 1 + (Real.pi * const1) / Real.pi ∧
      2.38 * 2.38 ≤ x4 ∧ x4 ≤ 3.01 * 3.01 ∧
      2 * 2 ≤ x5 ∧ x5 ≤ 2.52 * 2.52 ∧
      3.15 / 1.26 * 3.15 / 1.26 ≤ x6 ∧ x6 ≤ 15.53 →
        num1 x1 x2 x3 x4 x5 x6 * (-1) < 0 := by
  intro x1 x2 x3 x4 x5 x6 h
  rcases h with
    ⟨hx1_lower, hx1_upper,
     hx2_lower, hx2_upper,
     hx3_lower, hx3_upper,
     hx4_lower, hx4_upper,
     hx5_lower, hx5_upper,
     hx6_lower, _hx6_upper⟩
  have hx4_lower_num : 5.6644 ≤ x4 := by
    norm_num at hx4_lower ⊢
    exact hx4_lower
  have hx4_upper_num : x4 ≤ 9.0601 := by
    norm_num at hx4_upper ⊢
    exact hx4_upper
  have hx5_lower_num : 4 ≤ x5 := by
    norm_num at hx5_lower ⊢
    exact hx5_lower
  have hx5_upper_num : x5 ≤ 6.3504 := by
    norm_num at hx5_upper ⊢
    exact hx5_upper
  have hx6_lower_num : 6.25 ≤ x6 := by
    norm_num at hx6_lower ⊢
    exact hx6_lower
  have hpi_cancel : (Real.pi * const1) / Real.pi = const1 := by
    field_simp [Real.pi_pos.ne']
  rw [hpi_cancel] at hx1_upper hx2_upper hx3_upper
  have hx1_upper_six_fifths : x1 ≤ (6 : ℝ) / 5 := by
    calc
      x1 ≤ 1 + const1 := hx1_upper
      _ ≤ 1 + (1 : ℝ) / 5 := add_le_add_right const1_le_one_fifth 1
      _ = (6 : ℝ) / 5 := by norm_num
  have hx2_upper_six_fifths : x2 ≤ (6 : ℝ) / 5 := by
    calc
      x2 ≤ 1 + const1 := hx2_upper
      _ ≤ 1 + (1 : ℝ) / 5 := add_le_add_right const1_le_one_fifth 1
      _ = (6 : ℝ) / 5 := by norm_num
  have hx3_upper_six_fifths : x3 ≤ (6 : ℝ) / 5 := by
    calc
      x3 ≤ 1 + const1 := hx3_upper
      _ ≤ 1 + (1 : ℝ) / 5 := add_le_add_right const1_le_one_fifth 1
      _ = (6 : ℝ) / 5 := by norm_num
  have hcore :
      (x4 ^ 2) * x1 + 8 * (x5 - x6) * (x2 - x3)
          - x4 * (16 * x1 + (x5 - 8) * x2 + (x6 - 8) * x3) < 0 := by
    exact core_box_bound hx1_lower hx2_lower hx2_upper_six_fifths
      hx3_lower hx3_upper_six_fifths hx4_lower_num hx4_upper_num
      hx5_lower_num hx5_upper_num hx6_lower_num
  have h_target_identity :
      num1 x1 x2 x3 x4 x5 x6 * (-1) =
        4 * ((x4 ^ 2) * x1 + 8 * (x5 - x6) * (x2 - x3)
          - x4 * (16 * x1 + (x5 - 8) * x2 + (x6 - 8) * x3)) := by
    unfold num1
    ring
  rw [h_target_identity]
  exact mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 4) hcore
