import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

theorem ex4_ba :
    ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 →
      |Real.log (1 + x) - x| - 0.1 ≤ x * x := by
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hx1 : x ≤ 1 := hx.2
  have h1x_pos : 0 < 1 + x := by linarith
  have hlog_upper : Real.log (1 + x) ≤ x := by
    have h := Real.log_le_sub_one_of_pos h1x_pos
    linarith
  have hdiff_nonpos : Real.log (1 + x) - x ≤ 0 := by linarith
  have habs : |Real.log (1 + x) - x| = x - Real.log (1 + x) := by
    rw [abs_of_nonpos hdiff_nonpos]
    ring
  have hlog_lower : 2 * x / (x + 2) ≤ Real.log (1 + x) := by
    simpa using Real.le_log_one_add_of_nonneg hx0
  have hdiff_le_div : x - Real.log (1 + x) ≤ x * x / (x + 2) := by
    calc
      x - Real.log (1 + x) ≤ x - 2 * x / (x + 2) := sub_le_sub_left hlog_lower x
      _ = x * x / (x + 2) := by
        field_simp [show x + 2 ≠ 0 by linarith]
        ring
  have hden_pos : 0 < x + 2 := by linarith
  have hsq_nonneg : 0 ≤ x * x := mul_nonneg hx0 hx0
  have hdiv_le_sq : x * x / (x + 2) ≤ x * x := by
    rw [div_le_iff₀ hden_pos]
    have hden_ge_one : 1 ≤ x + 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hden_ge_one hsq_nonneg
    simpa [one_mul] using hmul
  have habs_le_sq : |Real.log (1 + x) - x| ≤ x * x := by
    rw [habs]
    exact hdiff_le_div.trans hdiv_le_sq
  linarith
