import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

theorem sin6sqrt2 :
    1.517 ≤ Real.sin (6 * Real.pi / 180) + Real.sqrt 2
    ∧ Real.sin (6 * Real.pi / 180) + Real.sqrt 2 ≤ 1.520 := by
  have hangle_eq : 6 * Real.pi / 180 = Real.pi / 30 := by
    ring
  have hangle_pos : 0 < 6 * Real.pi / 180 := by
    rw [hangle_eq]
    positivity
  have hangle_nonneg : 0 ≤ 6 * Real.pi / 180 := hangle_pos.le
  have hangle_upper : 6 * Real.pi / 180 ≤ (0.105 : ℝ) := by
    rw [hangle_eq]
    calc
      Real.pi / 30 ≤ (3.15 : ℝ) / 30 := by
        exact div_le_div_of_nonneg_right Real.pi_lt_d2.le (by norm_num)
      _ = (0.105 : ℝ) := by norm_num
  have hangle_lower : (157 / 1500 : ℝ) ≤ 6 * Real.pi / 180 := by
    rw [hangle_eq]
    calc
      (157 / 1500 : ℝ) = (3.14 : ℝ) / 30 := by norm_num
      _ ≤ Real.pi / 30 := by
        exact div_le_div_of_nonneg_right Real.pi_gt_d2.le (by norm_num)
  have hsqrt_lower : (1.414 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt' (by norm_num)]
    norm_num
  have hsqrt_upper : Real.sqrt 2 ≤ (1.415 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hsin_upper : Real.sin (6 * Real.pi / 180) ≤ (0.105 : ℝ) := by
    exact (Real.sin_le hangle_nonneg).trans hangle_upper
  have hangle_le_one : 6 * Real.pi / 180 ≤ (1 : ℝ) := hangle_upper.trans (by norm_num)
  have hsin_poly :
      6 * Real.pi / 180 - (6 * Real.pi / 180) ^ 3 / 4 <
        Real.sin (6 * Real.pi / 180) :=
    Real.sin_gt_sub_cube hangle_pos hangle_le_one
  have hangle_cube_upper : (6 * Real.pi / 180) ^ 3 ≤ (0.105 : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ hangle_nonneg hangle_upper 3
  have hpoly_lower :
      (0.104 : ℝ) ≤ 6 * Real.pi / 180 - (6 * Real.pi / 180) ^ 3 / 4 := by
    nlinarith
  have hsin_lower : (0.104 : ℝ) ≤ Real.sin (6 * Real.pi / 180) := by
    linarith
  constructor
  · linarith
  · linarith
