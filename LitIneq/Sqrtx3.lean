import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

theorem sqrtx3 :
    ∀ x : ℝ, 1 ≤ x ∧ x ≤ 2 →
      Real.sqrt x + Real.sqrt 3 < Real.pi + 0.01 := by
  intro x hx
  have hsqrt_le : Real.sqrt x ≤ Real.sqrt 2 := Real.sqrt_le_sqrt hx.2
  have hsqrt2_lt : Real.sqrt 2 < (99 : ℝ) / 70 := by
    have hsq : 2 < ((99 : ℝ) / 70) ^ 2 := by norm_num
    calc
      Real.sqrt 2 < Real.sqrt (((99 : ℝ) / 70) ^ 2) :=
        Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) hsq
      _ = (99 : ℝ) / 70 := by
        rw [Real.sqrt_sq_eq_abs]
        exact abs_of_pos (by norm_num : 0 < (99 : ℝ) / 70)
  have hsqrt3_lt : Real.sqrt 3 < (97 : ℝ) / 56 := by
    have hsq : 3 < ((97 : ℝ) / 56) ^ 2 := by norm_num
    calc
      Real.sqrt 3 < Real.sqrt (((97 : ℝ) / 56) ^ 2) :=
        Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 3) hsq
      _ = (97 : ℝ) / 56 := by
        rw [Real.sqrt_sq_eq_abs]
        exact abs_of_pos (by norm_num : 0 < (97 : ℝ) / 56)
  have hsum_lt : Real.sqrt 2 + Real.sqrt 3 < (881 : ℝ) / 280 := by
    nlinarith
  have hmid : (881 : ℝ) / 280 < (63 : ℝ) / 20 := by norm_num
  have hpi_lb : (63 : ℝ) / 20 < Real.pi + 0.01 := by
    nlinarith [Real.pi_gt_d2]
  calc
    Real.sqrt x + Real.sqrt 3 ≤ Real.sqrt 2 + Real.sqrt 3 := by
      exact add_le_add_left hsqrt_le (Real.sqrt 3)
    _ < (881 : ℝ) / 280 := hsum_lt
    _ < (63 : ℝ) / 20 := hmid
    _ < Real.pi + 0.01 := hpi_lb
