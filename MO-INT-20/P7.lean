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

namespace Lean92.MO_INT_20_P7

theorem P7 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by
  let x1 : ℝ := a*b
  let x2 : ℝ := b
  let x3 : ℝ := 1
  have hx1 : x1 > 0 := by dsimp [x1]; positivity
  have hx2 : x2 > 0 := by dsimp [x2]; positivity
  have hx3 : x3 > 0 := by dsimp [x3]; positivity
  have ha_ne : a ≠ 0 := by positivity
  have hb_ne : b ≠ 0 := by positivity
  have hc_ne : c ≠ 0 := by positivity
  have ha_repr : a = x1 / x2 := by
    dsimp [x1, x2]
    field_simp [hb_ne]
  have hb_repr : b = x2 / x3 := by
    dsimp [x2, x3]
    ring
  have hc_repr : c = x3 / x1 := by
    dsimp [x3, x1]
    have h_prod_tail : c * (a*b) = 1 := by nlinarith [h]
    field_simp [ha_ne, hb_ne]
    nlinarith [h_prod_tail]
  rw [ha_repr, hb_repr, hc_repr]
  rw [← sub_nonneg]
  suffices hnum :
      0 ≤ x1^3 - x1^2*x2 - x1^2*x3 - x1*x2^2 + 3*x1*x2*x3 - x1*x3^2 + x2^3 - x2^2*x3 - x2*x3^2 + x3^3 by
    have h_ratio_den_factor1_ne : x2 ≠ 0 := by positivity
    have h_ratio_den_factor2_ne : x3 ≠ 0 := by positivity
    have h_ratio_den_factor3_ne : x1 ≠ 0 := by positivity
    have h_ratio_den_pos : 0 < x1*x2*x3 := by positivity
    have h_ratio_den_ne : x1*x2*x3 ≠ 0 := ne_of_gt h_ratio_den_pos
    have h_ratio_den_nonneg : 0 ≤ x1*x2*x3 := h_ratio_den_pos.le
    have h_ratio_frac : 0 ≤ (x1^3 - x1^2*x2 - x1^2*x3 - x1*x2^2 + 3*x1*x2*x3 - x1*x3^2 + x2^3 - x2^2*x3 - x2*x3^2 + x3^3) / (x1*x2*x3) := by
      exact div_nonneg hnum h_ratio_den_nonneg
    convert h_ratio_frac using 1
    field_simp [hx1.ne.symm, hx2.ne.symm, hx3.ne.symm, h_ratio_den_factor1_ne, h_ratio_den_factor2_ne, h_ratio_den_factor3_ne, h_ratio_den_ne]
    ring_nf
  have hDS_class_1 : ∀ x1 x2 x3 : ℝ, 0 ≤ x1 → 0 ≤ x2 → 0 ≤ x3 → x1 ≤ x2 ∧ x2 ≤ x3 → 0 ≤ x1^3 - x1^2*x2 - x1^2*x3 - x1*x2^2 + 3*x1*x2*x3 - x1*x3^2 + x2^3 - x2^2*x3 - x2*x3^2 + x3^3 := by
    intro x1 x2 x3 h_x1_nonneg_base h_x2_nonneg_base h_x3_nonneg_base hsort
    have h_x1_x2 : x1 ≤ x2 := hsort.1
    have h_x2_x3 : x2 ≤ x3 := hsort.2
    set t1_1 := x1
    set t1_2 := x2 - x1
    set t1_3 := x3 - x2
    have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
    have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
    have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
    have h_x2_eq : x2 = t1_1 + t1_2 := by
      dsimp [t1_1, t1_2]
      ring_nf
    have h_x3_eq : x3 = t1_1 + t1_2 + t1_3 := by
      dsimp [t1_1, t1_2, t1_3]
      ring_nf
    rw [h_x2_eq, h_x3_eq]
    ring_nf
    positivity
  have h_x2_x1 := le_total x2 x1
  rcases h_x2_x1 with h_x2_x1 | h_x1_x2
  ·
    have h_x3_x2 := le_total x3 x2
    rcases h_x3_x2 with h_x3_x2 | h_x2_x3
    ·
      have hs : x3 ≤ x2 ∧ x2 ≤ x1 := by
        constructor
        · linarith
        ·
          linarith
      have hcert := hDS_class_1 x3 x2 x1 (by positivity) (by positivity) (by positivity) hs
      convert hcert using 1 <;> ring_nf
    ·
      have h_x3_x1 := le_total x3 x1
      rcases h_x3_x1 with h_x3_x1 | h_x1_x3
      ·
        have hs : x2 ≤ x3 ∧ x3 ≤ x1 := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 x2 x3 x1 (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf
      ·
        have hs : x2 ≤ x1 ∧ x1 ≤ x3 := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 x2 x1 x3 (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf
  ·
    have h_x3_x1 := le_total x3 x1
    rcases h_x3_x1 with h_x3_x1 | h_x1_x3
    ·
      have hs : x3 ≤ x1 ∧ x1 ≤ x2 := by
        constructor
        · linarith
        ·
          linarith
      have hcert := hDS_class_1 x3 x1 x2 (by positivity) (by positivity) (by positivity) hs
      convert hcert using 1 <;> ring_nf
    ·
      have h_x3_x2 := le_total x3 x2
      rcases h_x3_x2 with h_x3_x2 | h_x2_x3
      ·
        have hs : x1 ≤ x3 ∧ x3 ≤ x2 := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 x1 x3 x2 (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf
      ·
        have hs : x1 ≤ x2 ∧ x2 ≤ x3 := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 x1 x2 x3 (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf

end Lean92.MO_INT_20_P7


theorem P7 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a * b * c = 1) : (a - 1 + 1 / b) * (b - 1 + 1 / c) * (c - 1 + 1 / a) ≤ 1 := by
  exact @Lean92.MO_INT_20_P7.P7 a b c ha hb hc h

#print axioms P7
