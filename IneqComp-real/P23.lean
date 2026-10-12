import Mathlib

theorem real_p23 (a b : ℝ) (ha : a > 0) (hb : b > 0) (hab : a > b) : √2 * a^3 + 3 / (a * b - b^2) ≥ 10 := by
  have hba_pos : 0 < a - b := sub_pos.mpr hab
  have hden_pos : 0 < a * b - b^2 := by
    have hprod_pos : 0 < b * (a - b) := mul_pos hb hba_pos
    nlinarith
  have ha2_pos : 0 < a^2 := pow_pos ha 2
  have hden_bound : 4 * (a * b - b^2) ≤ a^2 := by
    nlinarith [sq_nonneg (a - 2 * b)]
  have hfrac_bound : 12 / a^2 ≤ 3 / (a * b - b^2) := by
    rw [div_le_div_iff₀ ha2_pos hden_pos]
    nlinarith [hden_bound]
  have hsqrt2_sq : (√2 : ℝ)^2 = 2 := by
    rw [Real.sq_sqrt]
    norm_num
  have hsqrt2_cube : (√2 : ℝ)^3 = 2 * √2 := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hsqrt2_sq]
  have hpoly_factor :
      √2 * a^5 - 10 * a^2 + 12 =
        (a - √2)^2 * (√2 * a^3 + 4 * a^2 + 6 * √2 * a + 6) := by
    ring_nf
    rw [hsqrt2_cube, hsqrt2_sq]
    ring
  have hquot_pos : 0 < √2 * a^3 + 4 * a^2 + 6 * √2 * a + 6 := by
    have hsqrt2_nonneg : 0 ≤ (√2 : ℝ) := Real.sqrt_nonneg 2
    have ha3_pos : 0 < a^3 := pow_pos ha 3
    have hterm1_nonneg : 0 ≤ √2 * a^3 := mul_nonneg hsqrt2_nonneg ha3_pos.le
    have hterm2_nonneg : 0 ≤ 4 * a^2 := by positivity
    have hterm3_nonneg : 0 ≤ 6 * √2 * a := by positivity
    nlinarith
  have hpoly_nonneg : 0 ≤ √2 * a^5 - 10 * a^2 + 12 := by
    rw [hpoly_factor]
    exact mul_nonneg (sq_nonneg (a - √2)) hquot_pos.le
  have hone_variable : 10 ≤ √2 * a^3 + 12 / a^2 := by
    have hrewrite :
        √2 * a^3 + 12 / a^2 - 10 =
          (√2 * a^5 - 10 * a^2 + 12) / a^2 := by
      field_simp [ne_of_gt ha2_pos]
      ring
    have hnonneg : 0 ≤ √2 * a^3 + 12 / a^2 - 10 := by
      rw [hrewrite]
      exact div_nonneg hpoly_nonneg ha2_pos.le
    linarith
  exact le_trans hone_variable (by
    simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hfrac_bound (√2 * a^3))
