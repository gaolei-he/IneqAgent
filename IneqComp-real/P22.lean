import Mathlib

theorem real_p22 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : Real.log a + Real.log b + Real.log c ≤ Real.log ((a + b) / 2) + Real.log ((b + c) / 2) + Real.log ((c + a) / 2) := by
  have h_amgm_ab : Real.sqrt (a * b) ≤ (a + b) / 2 := by
    have hsq : (Real.sqrt (a * b)) ^ 2 = a * b := by
      exact Real.sq_sqrt (mul_nonneg ha.le hb.le)
    have htwo : 2 * Real.sqrt (a * b) ≤ a + b := by
      exact two_mul_le_add_of_sq_le_mul ha.le hb.le (by rw [hsq])
    nlinarith
  have h_log_amgm_ab : Real.log (Real.sqrt (a * b)) ≤ Real.log ((a + b) / 2) := by
    exact Real.log_le_log (Real.sqrt_pos.2 (mul_pos ha hb)) h_amgm_ab
  have h_conc_ab : (Real.log a + Real.log b) / 2 ≤ Real.log ((a + b) / 2) := by
    calc
      (Real.log a + Real.log b) / 2 = Real.log (Real.sqrt (a * b)) := by
        rw [Real.log_sqrt (mul_nonneg ha.le hb.le), Real.log_mul ha.ne' hb.ne']
      _ ≤ Real.log ((a + b) / 2) := h_log_amgm_ab
  have h_amgm_bc : Real.sqrt (b * c) ≤ (b + c) / 2 := by
    have hsq : (Real.sqrt (b * c)) ^ 2 = b * c := by
      exact Real.sq_sqrt (mul_nonneg hb.le hc.le)
    have htwo : 2 * Real.sqrt (b * c) ≤ b + c := by
      exact two_mul_le_add_of_sq_le_mul hb.le hc.le (by rw [hsq])
    nlinarith
  have h_log_amgm_bc : Real.log (Real.sqrt (b * c)) ≤ Real.log ((b + c) / 2) := by
    exact Real.log_le_log (Real.sqrt_pos.2 (mul_pos hb hc)) h_amgm_bc
  have h_conc_bc : (Real.log b + Real.log c) / 2 ≤ Real.log ((b + c) / 2) := by
    calc
      (Real.log b + Real.log c) / 2 = Real.log (Real.sqrt (b * c)) := by
        rw [Real.log_sqrt (mul_nonneg hb.le hc.le), Real.log_mul hb.ne' hc.ne']
      _ ≤ Real.log ((b + c) / 2) := h_log_amgm_bc
  have h_amgm_ca : Real.sqrt (c * a) ≤ (c + a) / 2 := by
    have hsq : (Real.sqrt (c * a)) ^ 2 = c * a := by
      exact Real.sq_sqrt (mul_nonneg hc.le ha.le)
    have htwo : 2 * Real.sqrt (c * a) ≤ c + a := by
      exact two_mul_le_add_of_sq_le_mul hc.le ha.le (by rw [hsq])
    nlinarith
  have h_log_amgm_ca : Real.log (Real.sqrt (c * a)) ≤ Real.log ((c + a) / 2) := by
    exact Real.log_le_log (Real.sqrt_pos.2 (mul_pos hc ha)) h_amgm_ca
  have h_conc_ca : (Real.log c + Real.log a) / 2 ≤ Real.log ((c + a) / 2) := by
    calc
      (Real.log c + Real.log a) / 2 = Real.log (Real.sqrt (c * a)) := by
        rw [Real.log_sqrt (mul_nonneg hc.le ha.le), Real.log_mul hc.ne' ha.ne']
      _ ≤ Real.log ((c + a) / 2) := h_log_amgm_ca
  have h_pair_sum :
      (Real.log a + Real.log b) / 2 + (Real.log b + Real.log c) / 2 +
          (Real.log c + Real.log a) / 2 ≤
        Real.log ((a + b) / 2) + Real.log ((b + c) / 2) + Real.log ((c + a) / 2) := by
    exact add_le_add (add_le_add h_conc_ab h_conc_bc) h_conc_ca
  have h_left_eq :
      (Real.log a + Real.log b) / 2 + (Real.log b + Real.log c) / 2 +
          (Real.log c + Real.log a) / 2 = Real.log a + Real.log b + Real.log c := by
    ring
  rw [h_left_eq] at h_pair_sum
  exact h_pair_sum
