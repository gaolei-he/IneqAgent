import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

theorem Tunnel_3_IL_LU :
    ∀ x : ℝ, 0 ≤ x ∧ x ≤ 8.17 * (10 : ℝ) ^ (-8 : ℤ) →
      0 ≤
        -0.0006427443996 * Real.exp (-2.559889987 * ((10 : ℝ) ^ 8 * x))
          - 0.07600397043
          + 0.1443470449 * Real.exp (-4.211001275 * ((10 : ℝ) ^ 6 * x))
      ∧
        -0.0006427443996 * Real.exp (-2.559889987 * ((10 : ℝ) ^ 8 * x))
          - 0.07600397043
          + 0.1443470449 * Real.exp (-4.211001275 * ((10 : ℝ) ^ 6 * x)) ≤ 0.08 := by
  intro x hx
  have hx_nonneg : 0 ≤ x := hx.1
  have hx_le : x ≤ 8.17 * (10 : ℝ) ^ (-8 : ℤ) := hx.2
  have hpow8_pos : 0 < (10 : ℝ) ^ 8 := by norm_num
  have hpow6_pos : 0 < (10 : ℝ) ^ 6 := by norm_num
  have hx_scaled8_nonneg : 0 ≤ (10 : ℝ) ^ 8 * x := by
    exact mul_nonneg (le_of_lt hpow8_pos) hx_nonneg
  have hx_scaled6_nonneg : 0 ≤ (10 : ℝ) ^ 6 * x := by
    exact mul_nonneg (le_of_lt hpow6_pos) hx_nonneg
  have hx_scaled6_le : (10 : ℝ) ^ 6 * x ≤ 0.0817 := by
    calc
      (10 : ℝ) ^ 6 * x ≤ (10 : ℝ) ^ 6 * (8.17 * (10 : ℝ) ^ (-8 : ℤ)) := by
        exact mul_le_mul_of_nonneg_left hx_le (le_of_lt hpow6_pos)
      _ = 0.0817 := by norm_num
  have harg8_nonpos : -2.559889987 * ((10 : ℝ) ^ 8 * x) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hx_scaled8_nonneg
  have harg6_nonpos : -4.211001275 * ((10 : ℝ) ^ 6 * x) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) hx_scaled6_nonneg
  have harg6_lower : -0.3440388041675 ≤ -4.211001275 * ((10 : ℝ) ^ 6 * x) := by
    nlinarith [hx_scaled6_le]
  have hexp8_pos : 0 < Real.exp (-2.559889987 * ((10 : ℝ) ^ 8 * x)) := Real.exp_pos _
  have hexp8_le_one : Real.exp (-2.559889987 * ((10 : ℝ) ^ 8 * x)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr harg8_nonpos
  have hexp6_le_one : Real.exp (-4.211001275 * ((10 : ℝ) ^ 6 * x)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr harg6_nonpos
  have hexp6_ge_point6 : 0.6 ≤ Real.exp (-4.211001275 * ((10 : ℝ) ^ 6 * x)) := by
    have hlinear : (0.6 : ℝ) ≤ 1 + (-0.3440388041675 : ℝ) := by norm_num
    have hbase : 1 + (-0.3440388041675 : ℝ) ≤ Real.exp (-0.3440388041675 : ℝ) := by
      simpa [add_comm] using Real.add_one_le_exp (-0.3440388041675 : ℝ)
    have hmono : Real.exp (-0.3440388041675 : ℝ) ≤
        Real.exp (-4.211001275 * ((10 : ℝ) ^ 6 * x)) := by
      exact Real.exp_le_exp.mpr harg6_lower
    linarith
  have hnegterm_lower :
      -0.0006427443996 ≤
        -0.0006427443996 * Real.exp (-2.559889987 * ((10 : ℝ) ^ 8 * x)) := by
    have hmul :
        0.0006427443996 * Real.exp (-2.559889987 * ((10 : ℝ) ^ 8 * x)) ≤
          0.0006427443996 * 1 := by
      exact mul_le_mul_of_nonneg_left hexp8_le_one (by norm_num)
    nlinarith
  have hposterm_lower :
      0.1443470449 * 0.6 ≤
        0.1443470449 * Real.exp (-4.211001275 * ((10 : ℝ) ^ 6 * x)) := by
    exact mul_le_mul_of_nonneg_left hexp6_ge_point6 (by norm_num)
  have hlower :
      0 ≤
        -0.0006427443996 * Real.exp (-2.559889987 * ((10 : ℝ) ^ 8 * x))
          - 0.07600397043
          + 0.1443470449 * Real.exp (-4.211001275 * ((10 : ℝ) ^ 6 * x)) := by
    nlinarith [hnegterm_lower, hposterm_lower]
  have hnegterm_nonpos :
      -0.0006427443996 * Real.exp (-2.559889987 * ((10 : ℝ) ^ 8 * x)) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (le_of_lt hexp8_pos)
  have hposterm_upper :
      0.1443470449 * Real.exp (-4.211001275 * ((10 : ℝ) ^ 6 * x)) ≤ 0.1443470449 := by
    have hmul :
        0.1443470449 * Real.exp (-4.211001275 * ((10 : ℝ) ^ 6 * x)) ≤
          0.1443470449 * 1 := by
      exact mul_le_mul_of_nonneg_left hexp6_le_one (by norm_num)
    nlinarith
  have hupper :
      -0.0006427443996 * Real.exp (-2.559889987 * ((10 : ℝ) ^ 8 * x))
          - 0.07600397043
          + 0.1443470449 * Real.exp (-4.211001275 * ((10 : ℝ) ^ 6 * x)) ≤ 0.08 := by
    nlinarith [hnegterm_nonpos, hposterm_upper]
  exact ⟨hlower, hupper⟩
