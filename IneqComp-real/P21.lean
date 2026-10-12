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

namespace Lean92.IneqComp_real_P21

theorem real_p21 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : (a + 1 / b) * (b + 1 / c) * (c + 1 / a) ≥ 1000 / 27 := by
  rw [ge_iff_le]
  rw [← sub_nonneg]
  have hden1_pos : 0 < a := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden1_ne : a ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < b := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden2_ne : b ≠ 0 := ne_of_gt hden2_pos
  have hden3_pos : 0 < c := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden3_ne : c ≠ 0 := ne_of_gt hden3_pos
  field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm, hden1_pos, hden2_pos, hden3_pos, hden1_ne, hden2_ne, hden3_ne]
  ring_nf
  have hQ : a + b + c = 1 := by nlinarith [h]
  have hQunit : a + b + c = 1 := by nlinarith [hQ]
  suffices hH :
      0 ≤ 27*a^2*b^2*c^2 + 27*a^2*b*c*(a + b + c)^2 + 27*a*b^2*c*(a + b + c)^2 + 27*a*b*c^2*(a + b + c)^2 - 1000*a*b*c*(a + b + c)^3 + 27*a*b*(a + b + c)^4 + 27*a*c*(a + b + c)^4 + 27*b*c*(a + b + c)^4 + 27*(a + b + c)^6 by
    convert hH using 1
    try rw [hQunit]
    try rw [hQ]
    ring_nf
  ring_nf
  clear h hQ hQunit
  clear hden1_pos hden2_pos hden3_pos hden1_ne hden2_ne hden3_ne
  have hDS_class_1 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ 27*a^6 + 189*a^5*b + 189*a^5*c + 513*a^4*b^2 + 80*a^4*b*c + 513*a^4*c^2 + 702*a^3*b^3 - 705*a^3*b^2*c - 705*a^3*b*c^2 + 702*a^3*c^3 + 513*a^2*b^4 - 705*a^2*b^3*c - 2409*a^2*b^2*c^2 - 705*a^2*b*c^3 + 513*a^2*c^4 + 189*a*b^5 + 80*a*b^4*c - 705*a*b^3*c^2 - 705*a*b^2*c^3 + 80*a*b*c^4 + 189*a*c^5 + 27*b^6 + 189*b^5*c + 513*b^4*c^2 + 702*b^3*c^3 + 513*b^2*c^4 + 189*b*c^5 + 27*c^6 := by
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

end Lean92.IneqComp_real_P21


theorem real_p21 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : (a + 1 / b) * (b + 1 / c) * (c + 1 / a) ≥ 1000 / 27 := by
  exact @Lean92.IneqComp_real_P21.real_p21 a b c ha hb hc h

#print axioms real_p21
