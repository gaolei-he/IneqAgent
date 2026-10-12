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

namespace Lean92.MO_INT_20_P16

theorem P16 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h : a + b + c = 1) : 1 / (a^2 - 4*a + 9) + 1 / (b^2 - 4*b + 9) + 1 / (c^2 - 4*c + 9) ≤ 7 / 18 := by
  rw [← sub_nonneg]
  have hden1_pos : 0 < a*(a - 4) + 9 := by
    nlinarith [sq_nonneg (a - 2)]
  have hden1_ne : a*(a - 4) + 9 ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < b*(b - 4) + 9 := by
    nlinarith [sq_nonneg (b - 2)]
  have hden2_ne : b*(b - 4) + 9 ≠ 0 := ne_of_gt hden2_pos
  have hden3_pos : 0 < c*(c - 4) + 9 := by
    nlinarith [sq_nonneg (c - 2)]
  have hden3_ne : c*(c - 4) + 9 ≠ 0 := ne_of_gt hden3_pos
  field_simp [hden1_pos, hden2_pos, hden3_pos, hden1_ne, hden2_ne, hden3_ne]
  ring_nf
  have hQ : a + b + c = 1 := by nlinarith [h]
  have hQunit : a + b + c = 1 := by nlinarith [hQ]
  suffices hH :
      0 ≤ 7*a^2*b^2*c^2 - 28*a^2*b^2*c*(a + b + c) + 45*a^2*b^2*(a + b + c)^2 - 28*a^2*b*c^2*(a + b + c) + 112*a^2*b*c*(a + b + c)^2 - 180*a^2*b*(a + b + c)^3 + 45*a^2*c^2*(a + b + c)^2 - 180*a^2*c*(a + b + c)^3 + 243*a^2*(a + b + c)^4 - 28*a*b^2*c^2*(a + b + c) + 112*a*b^2*c*(a + b + c)^2 - 180*a*b^2*(a + b + c)^3 + 112*a*b*c^2*(a + b + c)^2 - 448*a*b*c*(a + b + c)^3 + 720*a*b*(a + b + c)^4 - 180*a*c^2*(a + b + c)^3 + 720*a*c*(a + b + c)^4 - 972*a*(a + b + c)^5 + 45*b^2*c^2*(a + b + c)^2 - 180*b^2*c*(a + b + c)^3 + 243*b^2*(a + b + c)^4 - 180*b*c^2*(a + b + c)^3 + 720*b*c*(a + b + c)^4 - 972*b*(a + b + c)^5 + 243*c^2*(a + b + c)^4 - 972*c*(a + b + c)^5 + 729*(a + b + c)^6 by
    convert hH using 1
    try rw [hQunit]
    try rw [hQ]
    ring_nf
  ring_nf
  clear h hQ hQunit
  clear hden1_pos hden2_pos hden3_pos hden1_ne hden2_ne hden3_ne
  have hDS_class_1 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ 54*a^5*b + 54*a^5*c + 261*a^4*b^2 + 690*a^4*b*c + 261*a^4*c^2 + 414*a^3*b^3 + 1862*a^3*b^2*c + 1862*a^3*b*c^2 + 414*a^3*c^3 + 261*a^2*b^4 + 1862*a^2*b^3*c + 3226*a^2*b^2*c^2 + 1862*a^2*b*c^3 + 261*a^2*c^4 + 54*a*b^5 + 690*a*b^4*c + 1862*a*b^3*c^2 + 1862*a*b^2*c^3 + 690*a*b*c^4 + 54*a*c^5 + 54*b^5*c + 261*b^4*c^2 + 414*b^3*c^3 + 261*b^2*c^4 + 54*b*c^5 := by
    intro a b c h_a_nonneg_base h_b_nonneg_base h_c_nonneg_base hsort
    have h_a_b : a ≤ b := hsort.1
    have h_b_c : b ≤ c := hsort.2
    set t1_1 := a
    set t1_2 := b - a
    set t1_3 := c - b
    have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
    have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
    have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
    have h_b_eq : b = t1_1 + t1_2 := by
      dsimp [t1_1, t1_2]
      ring_nf
    have h_c_eq : c = t1_1 + t1_2 + t1_3 := by
      dsimp [t1_1, t1_2, t1_3]
      ring_nf
    rw [h_b_eq, h_c_eq]
    ring_nf
    positivity
  have h_b_a := le_total b a
  rcases h_b_a with h_b_a | h_a_b
  ·
    have h_c_b := le_total c b
    rcases h_c_b with h_c_b | h_b_c
    ·
      have hs : c ≤ b ∧ b ≤ a := by
        constructor
        · linarith
        ·
          linarith
      have hcert := hDS_class_1 c b a (by positivity) (by positivity) (by positivity) hs
      convert hcert using 1 <;> ring_nf
    ·
      have h_c_a := le_total c a
      rcases h_c_a with h_c_a | h_a_c
      ·
        have hs : b ≤ c ∧ c ≤ a := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 b c a (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf
      ·
        have hs : b ≤ a ∧ a ≤ c := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 b a c (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf
  ·
    have h_c_a := le_total c a
    rcases h_c_a with h_c_a | h_a_c
    ·
      have hs : c ≤ a ∧ a ≤ b := by
        constructor
        · linarith
        ·
          linarith
      have hcert := hDS_class_1 c a b (by positivity) (by positivity) (by positivity) hs
      convert hcert using 1 <;> ring_nf
    ·
      have h_c_b := le_total c b
      rcases h_c_b with h_c_b | h_b_c
      ·
        have hs : a ≤ c ∧ c ≤ b := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 a c b (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf
      ·
        have hs : a ≤ b ∧ b ≤ c := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 a b c (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf

end Lean92.MO_INT_20_P16


theorem P16 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h : a + b + c = 1) : 1 / (a^2 - 4*a + 9) + 1 / (b^2 - 4*b + 9) + 1 / (c^2 - 4*c + 9) ≤ 7 / 18 := by
  exact @Lean92.MO_INT_20_P16.P16 a b c ha hb hc h

#print axioms P16
