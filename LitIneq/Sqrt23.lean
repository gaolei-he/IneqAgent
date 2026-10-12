import Mathlib
open Real

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

theorem sqrt23 :
    0.002 ≤ Real.sqrt 2 + Real.sqrt 3 - Real.pi
    ∧ Real.sqrt 2 + Real.sqrt 3 - Real.pi ≤ 0.007 := by
  have hsqrt2_lo : (1.414 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt] <;> norm_num
  have hsqrt2_hi : Real.sqrt 2 ≤ (1.415 : ℝ) := by
    rw [Real.sqrt_le_left] <;> norm_num
  have hsqrt3_lo : (1.73 : ℝ) ≤ Real.sqrt 3 := by
    rw [Real.le_sqrt] <;> norm_num
  have hsqrt3_hi : Real.sqrt 3 ≤ (1.733 : ℝ) := by
    rw [Real.sqrt_le_left] <;> norm_num
  have hpi_lo : (3.1415 : ℝ) < Real.pi := by
    simpa using Real.pi_gt_d4
  have hpi_hi : Real.pi < (3.1416 : ℝ) := by
    simpa using Real.pi_lt_d4
  have hlower : 0.002 ≤ Real.sqrt 2 + Real.sqrt 3 - Real.pi := by
    nlinarith
  have hupper : Real.sqrt 2 + Real.sqrt 3 - Real.pi ≤ 0.007 := by
    nlinarith
  exact ⟨hlower, hupper⟩
