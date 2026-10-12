import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert
import Mathlib.Tactic.IntervalCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace Lean92.IneqComp_real_P46

theorem real_p46 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = 1) : y * z + z * x + x * y - 2 * x * y * z ≤ 7 / 27 := by
  rw [← sub_nonneg]
  field_simp [hx.ne.symm, hy.ne.symm, hz.ne.symm]
  ring_nf
  have hQ : x + y + z = 1 := by nlinarith [h]
  have hQunit : x + y + z = 1 := by nlinarith [hQ]
  suffices hH :
      0 ≤ 54*x*y*z - 27*x*y*(x + y + z) - 27*x*z*(x + y + z) - 27*y*z*(x + y + z) + 7*(x + y + z)^3 by
    convert hH using 1
    try rw [hQunit]
    try rw [hQ]
    ring_nf
  ring_nf
  clear h hQ hQunit
  have hDS_class_1 : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z → x ≤ y ∧ y ≤ z → 0 ≤ 7*x^3 - 6*x^2*y - 6*x^2*z - 6*x*y^2 + 15*x*y*z - 6*x*z^2 + 7*y^3 - 6*y^2*z - 6*y*z^2 + 7*z^3 := by
    intro x y z h_x_nonneg_base h_y_nonneg_base h_z_nonneg_base hsort
    have h_x_y : x ≤ y := hsort.1
    have h_y_z : y ≤ z := hsort.2
    set t1_1 := x
    set t1_2 := y - x
    set t1_3 := z - y
    have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
    have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
    have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
    have h_y_eq : y = t1_1 + t1_2 := by
      dsimp [t1_1, t1_2]
      ring_nf
    have h_z_eq : z = t1_1 + t1_2 + t1_3 := by
      dsimp [t1_1, t1_2, t1_3]
      ring_nf
    rw [h_y_eq, h_z_eq]
    ring_nf
    positivity
  have h_y_x := le_total y x
  rcases h_y_x with h_y_x | h_x_y
  ·
    have h_z_y := le_total z y
    rcases h_z_y with h_z_y | h_y_z
    ·
      have hs : z ≤ y ∧ y ≤ x := by
        constructor
        · linarith
        ·
          linarith
      have hcert := hDS_class_1 z y x (by positivity) (by positivity) (by positivity) hs
      convert hcert using 1 <;> ring_nf
    ·
      have h_z_x := le_total z x
      rcases h_z_x with h_z_x | h_x_z
      ·
        have hs : y ≤ z ∧ z ≤ x := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 y z x (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf
      ·
        have hs : y ≤ x ∧ x ≤ z := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 y x z (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf
  ·
    have h_z_x := le_total z x
    rcases h_z_x with h_z_x | h_x_z
    ·
      have hs : z ≤ x ∧ x ≤ y := by
        constructor
        · linarith
        ·
          linarith
      have hcert := hDS_class_1 z x y (by positivity) (by positivity) (by positivity) hs
      convert hcert using 1 <;> ring_nf
    ·
      have h_z_y := le_total z y
      rcases h_z_y with h_z_y | h_y_z
      ·
        have hs : x ≤ z ∧ z ≤ y := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 x z y (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf
      ·
        have hs : x ≤ y ∧ y ≤ z := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 x y z (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf

end Lean92.IneqComp_real_P46

open Real

theorem real_p46 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (h : x + y + z = 1) : y * z + z * x + x * y - 2 * x * y * z ≤ 7 / 27 := by
  exact @Lean92.IneqComp_real_P46.real_p46 x y z hx hy hz h

#print axioms real_p46
