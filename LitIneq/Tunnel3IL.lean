import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

theorem Tunnel_3_IL :
    ∀ x : ℝ, 0 ≤ x ∧ x ≤ 2.39 * (10 : ℝ) ^ (-9 : ℤ) →
      -0.0059 - 0.000016 * Real.exp (-2.55 * (10 : ℝ) ^ 8 * x)
        + 0.031 * Real.exp (-5.49 * (10 : ℝ) ^ 7 * x) ≤ 0.03 := by
  intro x hx
  have hx0 : 0 ≤ x := hx.1
  have hExpNonneg :
      0 ≤ Real.exp (-2.55 * (10 : ℝ) ^ 8 * x) := Real.exp_nonneg _
  have hArgNonpos : -5.49 * (10 : ℝ) ^ 7 * x ≤ 0 := by
    have hcoef_nonneg : 0 ≤ 5.49 * (10 : ℝ) ^ 7 * x := by
      positivity
    calc
      -5.49 * (10 : ℝ) ^ 7 * x = -(5.49 * (10 : ℝ) ^ 7 * x) := by ring
      _ ≤ 0 := neg_nonpos.mpr hcoef_nonneg
  have hSecondExpBound :
      Real.exp (-5.49 * (10 : ℝ) ^ 7 * x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact hArgNonpos
  have hneg_coeff : (-0.000016 : ℝ) ≤ 0 := by norm_num
  have hFirstNonpos :
      -0.000016 * Real.exp (-2.55 * (10 : ℝ) ^ 8 * x) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg hneg_coeff hExpNonneg
  have hSecondMulBound :
      0.031 * Real.exp (-5.49 * (10 : ℝ) ^ 7 * x) ≤ 0.031 := by
    exact mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ 0.031) hSecondExpBound
  nlinarith
