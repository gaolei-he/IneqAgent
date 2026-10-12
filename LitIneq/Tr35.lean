import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

private lemma tan_pi_div_36_le : Real.tan (Real.pi / 36) ≤ (7 : ℝ) / 80 := by
  have hp_ub : Real.pi / 36 < (1309 : ℝ) / 15000 := by
    nlinarith [Real.pi_lt_d4]
  have hq_lt_pi_half : (1309 : ℝ) / 15000 < Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have hmono : Real.tan (Real.pi / 36) ≤ Real.tan ((1309 : ℝ) / 15000) := by
    exact (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two
      (by positivity) hq_lt_pi_half hp_ub).le
  have hq_abs_le_one : |(1309 : ℝ) / 15000| ≤ 1 := by norm_num
  have hsin_q : Real.sin ((1309 : ℝ) / 15000) ≤
      (1309 : ℝ) / 15000 - ((1309 : ℝ) / 15000) ^ 3 / 6 +
        ((1309 : ℝ) / 15000) ^ 4 * (5 / 96 : ℝ) := by
    have h := (abs_sub_le_iff.mp (Real.sin_bound (x := ((1309 : ℝ) / 15000)) hq_abs_le_one)).1
    nlinarith
  have hcos_q_lb : 1 - ((1309 : ℝ) / 15000) ^ 2 / 2 -
        ((1309 : ℝ) / 15000) ^ 4 * (5 / 96 : ℝ) ≤
      Real.cos ((1309 : ℝ) / 15000) := by
    have h := (abs_sub_le_iff.mp (Real.cos_bound (x := ((1309 : ℝ) / 15000)) hq_abs_le_one)).2
    nlinarith
  have hcos_q_pos : 0 < Real.cos ((1309 : ℝ) / 15000) := by
    exact Real.cos_pos_of_le_one hq_abs_le_one
  have hq_ub : Real.tan ((1309 : ℝ) / 15000) ≤ (7 : ℝ) / 80 := by
    rw [Real.tan_eq_sin_div_cos]
    rw [div_le_iff₀ hcos_q_pos]
    nlinarith [hsin_q, hcos_q_lb]
  exact hmono.trans hq_ub

private lemma tan_35deg_le : Real.tan (35 * Real.pi / 180) ≤ (2801 : ℝ) / 4000 := by
  let p : ℝ := Real.pi / 36
  have hp_angle : 35 * Real.pi / 180 = Real.pi / 6 + p := by
    dsimp [p]
    ring
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]
    positivity
  have hcos_a_ne : ∀ k : ℤ, Real.pi / 6 ≠ (2 * k + 1) * Real.pi / 2 := by
    intro k hk
    exact (Real.cos_ne_zero_iff.mp (ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩))) k hk
  have hp_lt_half : p < Real.pi / 2 := by
    dsimp [p]
    nlinarith [Real.pi_pos]
  have hcos_p_ne : ∀ k : ℤ, p ≠ (2 * k + 1) * Real.pi / 2 := by
    intro k hk
    have hc : Real.cos p ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by dsimp [p]; nlinarith [Real.pi_pos], hp_lt_half⟩)
    exact (Real.cos_ne_zero_iff.mp hc) k hk
  have htan_p_nonneg : 0 ≤ Real.tan p := by
    exact Real.tan_nonneg_of_nonneg_of_le_pi_div_two hp_nonneg hp_lt_half.le
  have hp_lt_pi_div_three : p < Real.pi / 3 := by
    dsimp [p]
    nlinarith [Real.pi_pos]
  have htan_p_lt_sqrt3 : Real.tan p < Real.sqrt 3 := by
    have hmono : Real.tan p < Real.tan (Real.pi / 3) :=
      Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hp_nonneg
        (by nlinarith [Real.pi_pos]) hp_lt_pi_div_three
    simpa [Real.tan_pi_div_three] using hmono
  have hsqrt_ne : Real.sqrt 3 ≠ 0 := by positivity
  have hsub_ne : Real.sqrt 3 - Real.tan p ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr htan_p_lt_sqrt3)
  have htan_add_formula :
      Real.tan (Real.pi / 6 + p) =
        (1 + Real.sqrt 3 * Real.tan p) / (Real.sqrt 3 - Real.tan p) := by
    have hform := Real.tan_add' (x := Real.pi / 6) (y := p) ⟨hcos_a_ne, hcos_p_ne⟩
    rw [Real.tan_pi_div_six] at hform
    rw [hform]
    field_simp [hsqrt_ne, hsub_ne]
  have htan_p_le : Real.tan p ≤ (7 : ℝ) / 80 := by
    simpa [p] using tan_pi_div_36_le
  have hsqrt_lower : (173205 : ℝ) / 100000 ≤ Real.sqrt 3 := by
    exact Real.le_sqrt_of_sq_le (by norm_num)
  have hsqrt_upper : Real.sqrt 3 ≤ (173206 : ℝ) / 100000 := by
    rw [Real.sqrt_le_left (by positivity)]
    norm_num
  have hden_pos : 0 < Real.sqrt 3 - Real.tan p := sub_pos.mpr htan_p_lt_sqrt3
  rw [hp_angle, htan_add_formula]
  rw [div_le_iff₀ hden_pos]
  nlinarith [hsqrt_lower, hsqrt_upper, htan_p_le, htan_p_nonneg]

theorem tr_35 :
    ∀ phi v : ℝ,
      |phi| ≤ 35 →
      200 ≤ v ∧ v ≤ 250 →
        0 ≤ |180 * 9.8 * Real.tan (phi * Real.pi / 180) / (Real.pi * v * 0.514)|
        ∧ |180 * 9.8 * Real.tan (phi * Real.pi / 180) / (Real.pi * v * 0.514)| ≤ 3.825 := by
  intro phi v hphi hv
  have hv_lower : (200 : ℝ) ≤ v := hv.1
  have hv_upper : v ≤ (250 : ℝ) := hv.2
  have hv_pos : 0 < v := by
    linarith
  have hangle_abs_le : |phi * Real.pi / 180| ≤ 35 * Real.pi / 180 := by
    have hpi_nonneg : 0 ≤ Real.pi / 180 := by positivity
    calc
      |phi * Real.pi / 180| = |phi| * (Real.pi / 180) := by
        have hrewrite : phi * Real.pi / 180 = phi * (Real.pi / 180) := by ring
        rw [hrewrite, abs_mul, abs_of_nonneg hpi_nonneg]
      _ ≤ 35 * (Real.pi / 180) := by
        exact mul_le_mul_of_nonneg_right hphi hpi_nonneg
      _ = 35 * Real.pi / 180 := by
        ring
  have hangle_le : phi * Real.pi / 180 ≤ 35 * Real.pi / 180 := by
    exact (le_abs_self _).trans hangle_abs_le
  have hangle_neg_le : -(35 * Real.pi / 180) ≤ phi * Real.pi / 180 := by
    exact (abs_le.mp hangle_abs_le).1
  have hangle_endpoint_lt_half : 35 * Real.pi / 180 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have hangle_lt_half : phi * Real.pi / 180 < Real.pi / 2 :=
    hangle_le.trans_lt hangle_endpoint_lt_half
  have hangle_neg_half_lt : -(Real.pi / 2) < phi * Real.pi / 180 := by
    linarith
  have htan_abs_le_endpoint :
      |Real.tan (phi * Real.pi / 180)| ≤ Real.tan (35 * Real.pi / 180) := by
    by_cases hangle_nonneg : 0 ≤ phi * Real.pi / 180
    · have htan_nonneg :
          0 ≤ Real.tan (phi * Real.pi / 180) :=
        Real.tan_nonneg_of_nonneg_of_le_pi_div_two hangle_nonneg hangle_lt_half.le
      rw [abs_of_nonneg htan_nonneg]
      rcases eq_or_lt_of_le hangle_le with hangle_eq | hangle_lt
      · rw [hangle_eq]
      · exact (Real.tan_lt_tan_of_lt_of_lt_pi_div_two hangle_neg_half_lt
          hangle_endpoint_lt_half hangle_lt).le
    · have hangle_nonpos : phi * Real.pi / 180 ≤ 0 := le_of_not_ge hangle_nonneg
      have htan_nonpos :
          Real.tan (phi * Real.pi / 180) ≤ 0 :=
        Real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le hangle_nonpos hangle_neg_half_lt.le
      rw [abs_of_nonpos htan_nonpos]
      rw [← Real.tan_neg]
      have hneg_angle_nonneg : 0 ≤ -(phi * Real.pi / 180) := by
        linarith
      have hneg_angle_le : -(phi * Real.pi / 180) ≤ 35 * Real.pi / 180 := by
        linarith
      rcases eq_or_lt_of_le hneg_angle_le with hangle_eq | hangle_lt
      · rw [hangle_eq]
      · exact (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hneg_angle_nonneg
          hangle_endpoint_lt_half hangle_lt).le
  have hden_pos : 0 < Real.pi * v * 0.514 := by
    positivity
  have hden_lower : Real.pi * 200 * 0.514 ≤ Real.pi * v * 0.514 := by
    have hpi_scaled : Real.pi * 200 ≤ Real.pi * v :=
      mul_le_mul_of_nonneg_left hv_lower Real.pi_pos.le
    exact mul_le_mul_of_nonneg_right hpi_scaled (by norm_num)
  have hden200_pos : 0 < Real.pi * 200 * 0.514 := by
    positivity
  have htan35_nonneg : 0 ≤ Real.tan (35 * Real.pi / 180) := by
    exact Real.tan_nonneg_of_nonneg_of_le_pi_div_two (by positivity) hangle_endpoint_lt_half.le
  have htan_abs_bound : |Real.tan (phi * Real.pi / 180)| ≤ (2801 / 4000 : ℝ) := by
    exact htan_abs_le_endpoint.trans tan_35deg_le
  have hnum_le : |180 * 9.8 * Real.tan (phi * Real.pi / 180)| ≤
      1764 * (2801 / 4000 : ℝ) := by
    have hnum_eq : (180 : ℝ) * 9.8 = 1764 := by norm_num
    rw [hnum_eq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1764)]
    exact mul_le_mul_of_nonneg_left htan_abs_bound (by norm_num)
  have hstep1 :
      |180 * 9.8 * Real.tan (phi * Real.pi / 180) / (Real.pi * v * 0.514)| ≤
        (1764 * (2801 / 4000 : ℝ)) / (Real.pi * v * 0.514) := by
    rw [abs_div, abs_of_pos hden_pos]
    exact div_le_div_of_nonneg_right hnum_le (by positivity)
  have hstep2 :
      (1764 * (2801 / 4000 : ℝ)) / (Real.pi * v * 0.514) ≤
        (1764 * (2801 / 4000 : ℝ)) / (Real.pi * 200 * 0.514) := by
    exact div_le_div_of_nonneg_left (by positivity) hden200_pos hden_lower
  have hfinal_num :
      (1764 * (2801 / 4000 : ℝ)) / (Real.pi * 200 * 0.514) ≤ 3.825 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_d6]
  constructor
  · exact abs_nonneg _
  exact hstep1.trans (hstep2.trans hfinal_num)

end

end Leanpro.MetiTarskiExamplesSplit
