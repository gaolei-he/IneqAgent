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

namespace Lean92.Evan_chen_P18

theorem P18 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 3) : 6 ≤ 18 / ((3 - c) * (4 - c)) + 18 / ((3 - b) * (4 - b)) + 18 / ((3 - a) * (4 - a)) + 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  rw [← sub_nonneg]
  have hden1_pos : 0 < a*(a - 7) + 12 := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden1_ne : a*(a - 7) + 12 ≠ 0 := ne_of_gt hden1_pos
  have hden1_factor1_pos : 0 < 4 - a := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden1_factor1_ne : 4 - a ≠ 0 := ne_of_gt hden1_factor1_pos
  have hden1_factor2_pos : 0 < 3 - a := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden1_factor2_ne : 3 - a ≠ 0 := ne_of_gt hden1_factor2_pos
  have hden2_pos : 0 < b*(b - 7) + 12 := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden2_ne : b*(b - 7) + 12 ≠ 0 := ne_of_gt hden2_pos
  have hden2_factor1_pos : 0 < 4 - b := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden2_factor1_ne : 4 - b ≠ 0 := ne_of_gt hden2_factor1_pos
  have hden2_factor2_pos : 0 < 3 - b := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden2_factor2_ne : 3 - b ≠ 0 := ne_of_gt hden2_factor2_pos
  have hden3_pos : 0 < c*(c - 7) + 12 := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden3_ne : c*(c - 7) + 12 ≠ 0 := ne_of_gt hden3_pos
  have hden3_factor1_pos : 0 < 4 - c := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden3_factor1_ne : 4 - c ≠ 0 := ne_of_gt hden3_factor1_pos
  have hden3_factor2_pos : 0 < 3 - c := by
    first
    | positivity
    | nlinarith [ha, hb, hc, h]
  have hden3_factor2_ne : 3 - c ≠ 0 := ne_of_gt hden3_factor2_pos
  field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm, hden1_pos, hden1_factor1_pos, hden1_factor2_pos, hden2_pos, hden2_factor1_pos, hden2_factor2_pos, hden3_pos, hden3_factor1_pos, hden3_factor2_pos, hden1_ne, hden1_factor1_ne, hden1_factor2_ne, hden2_ne, hden2_factor1_ne, hden2_factor2_ne, hden3_ne, hden3_factor1_ne, hden3_factor2_ne]
  ring_nf
  have hQ : a + b + c = 3 := by nlinarith [h]
  have hQunit : a/3 + b/3 + c/3 = 1 := by nlinarith [hQ]
  suffices hH :
      0 ≤ 2*a^4*b^2*c^2 - 14*a^4*b^2*c*(a/3 + b/3 + c/3) + 24*a^4*b^2*(a/3 + b/3 + c/3)^2 - 14*a^4*b*c^2*(a/3 + b/3 + c/3) + 98*a^4*b*c*(a/3 + b/3 + c/3)^2 - 168*a^4*b*(a/3 + b/3 + c/3)^3 + 24*a^4*c^2*(a/3 + b/3 + c/3)^2 - 168*a^4*c*(a/3 + b/3 + c/3)^3 + 288*a^4*(a/3 + b/3 + c/3)^4 - 14*a^3*b^2*c^2*(a/3 + b/3 + c/3) + 98*a^3*b^2*c*(a/3 + b/3 + c/3)^2 - 168*a^3*b^2*(a/3 + b/3 + c/3)^3 + 98*a^3*b*c^2*(a/3 + b/3 + c/3)^2 - 686*a^3*b*c*(a/3 + b/3 + c/3)^3 + 1176*a^3*b*(a/3 + b/3 + c/3)^4 - 168*a^3*c^2*(a/3 + b/3 + c/3)^3 + 1176*a^3*c*(a/3 + b/3 + c/3)^4 - 2016*a^3*(a/3 + b/3 + c/3)^5 + 2*a^2*b^4*c^2 - 14*a^2*b^4*c*(a/3 + b/3 + c/3) + 24*a^2*b^4*(a/3 + b/3 + c/3)^2 - 14*a^2*b^3*c^2*(a/3 + b/3 + c/3) + 98*a^2*b^3*c*(a/3 + b/3 + c/3)^2 - 168*a^2*b^3*(a/3 + b/3 + c/3)^3 + 2*a^2*b^2*c^4 - 14*a^2*b^2*c^3*(a/3 + b/3 + c/3) + 66*a^2*b^2*c^2*(a/3 + b/3 + c/3)^2 - 294*a^2*b^2*c*(a/3 + b/3 + c/3)^3 + 522*a^2*b^2*(a/3 + b/3 + c/3)^4 - 14*a^2*b*c^4*(a/3 + b/3 + c/3) + 98*a^2*b*c^3*(a/3 + b/3 + c/3)^2 - 294*a^2*b*c^2*(a/3 + b/3 + c/3)^3 + 882*a^2*b*c*(a/3 + b/3 + c/3)^4 - 1638*a^2*b*(a/3 + b/3 + c/3)^5 + 24*a^2*c^4*(a/3 + b/3 + c/3)^2 - 168*a^2*c^3*(a/3 + b/3 + c/3)^3 + 522*a^2*c^2*(a/3 + b/3 + c/3)^4 - 1638*a^2*c*(a/3 + b/3 + c/3)^5 + 3024*a^2*(a/3 + b/3 + c/3)^6 - 14*a*b^4*c^2*(a/3 + b/3 + c/3) + 98*a*b^4*c*(a/3 + b/3 + c/3)^2 - 168*a*b^4*(a/3 + b/3 + c/3)^3 + 98*a*b^3*c^2*(a/3 + b/3 + c/3)^2 - 686*a*b^3*c*(a/3 + b/3 + c/3)^3 + 1176*a*b^3*(a/3 + b/3 + c/3)^4 - 14*a*b^2*c^4*(a/3 + b/3 + c/3) + 98*a*b^2*c^3*(a/3 + b/3 + c/3)^2 - 294*a*b^2*c^2*(a/3 + b/3 + c/3)^3 + 882*a*b^2*c*(a/3 + b/3 + c/3)^4 - 1638*a*b^2*(a/3 + b/3 + c/3)^5 + 98*a*b*c^4*(a/3 + b/3 + c/3)^2 - 686*a*b*c^3*(a/3 + b/3 + c/3)^3 + 882*a*b*c^2*(a/3 + b/3 + c/3)^4 + 2058*a*b*c*(a/3 + b/3 + c/3)^5 - 2646*a*b*(a/3 + b/3 + c/3)^6 - 168*a*c^4*(a/3 + b/3 + c/3)^3 + 1176*a*c^3*(a/3 + b/3 + c/3)^4 - 1638*a*c^2*(a/3 + b/3 + c/3)^5 - 2646*a*c*(a/3 + b/3 + c/3)^6 + 3024*a*(a/3 + b/3 + c/3)^7 + 24*b^4*c^2*(a/3 + b/3 + c/3)^2 - 168*b^4*c*(a/3 + b/3 + c/3)^3 + 288*b^4*(a/3 + b/3 + c/3)^4 - 168*b^3*c^2*(a/3 + b/3 + c/3)^3 + 1176*b^3*c*(a/3 + b/3 + c/3)^4 - 2016*b^3*(a/3 + b/3 + c/3)^5 + 24*b^2*c^4*(a/3 + b/3 + c/3)^2 - 168*b^2*c^3*(a/3 + b/3 + c/3)^3 + 522*b^2*c^2*(a/3 + b/3 + c/3)^4 - 1638*b^2*c*(a/3 + b/3 + c/3)^5 + 3024*b^2*(a/3 + b/3 + c/3)^6 - 168*b*c^4*(a/3 + b/3 + c/3)^3 + 1176*b*c^3*(a/3 + b/3 + c/3)^4 - 1638*b*c^2*(a/3 + b/3 + c/3)^5 - 2646*b*c*(a/3 + b/3 + c/3)^6 + 3024*b*(a/3 + b/3 + c/3)^7 + 288*c^4*(a/3 + b/3 + c/3)^4 - 2016*c^3*(a/3 + b/3 + c/3)^5 + 3024*c^2*(a/3 + b/3 + c/3)^6 + 3024*c*(a/3 + b/3 + c/3)^7 - 2592*(a/3 + b/3 + c/3)^8 by
    convert hH using 1
    try rw [hQunit]
    try rw [hQ]
    ring_nf
  ring_nf
  clear h hQ hQunit
  clear hden1_pos hden1_factor1_pos hden1_factor2_pos hden2_pos hden2_factor1_pos hden2_factor2_pos hden3_pos hden3_factor1_pos hden3_factor2_pos hden1_ne hden1_factor1_ne hden1_factor2_ne hden2_ne hden2_factor1_ne hden2_factor2_ne hden3_ne hden3_factor1_ne hden3_factor2_ne
  have hDS_class_1 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ 32*a^8/81 + 280*a^7*b/81 + 280*a^7*c/81 + 1010*a^6*b^2/81 + 230*a^6*b*c/9 + 1010*a^6*c^2/81 + 1600*a^5*b^3/81 + 4954*a^5*b^2*c/81 + 4954*a^5*b*c^2/81 + 1600*a^5*c^3/81 + 1676*a^4*b^4/81 + 6364*a^4*b^3*c/81 + 9394*a^4*b^2*c^2/81 + 6364*a^4*b*c^3/81 + 1676*a^4*c^4/81 + 1600*a^3*b^5/81 + 6364*a^3*b^4*c/81 + 10900*a^3*b^3*c^2/81 + 10900*a^3*b^2*c^3/81 + 6364*a^3*b*c^4/81 + 1600*a^3*c^5/81 + 1010*a^2*b^6/81 + 4954*a^2*b^5*c/81 + 9394*a^2*b^4*c^2/81 + 10900*a^2*b^3*c^3/81 + 9394*a^2*b^2*c^4/81 + 4954*a^2*b*c^5/81 + 1010*a^2*c^6/81 + 280*a*b^7/81 + 230*a*b^6*c/9 + 4954*a*b^5*c^2/81 + 6364*a*b^4*c^3/81 + 6364*a*b^3*c^4/81 + 4954*a*b^2*c^5/81 + 230*a*b*c^6/9 + 280*a*c^7/81 + 32*b^8/81 + 280*b^7*c/81 + 1010*b^6*c^2/81 + 1600*b^5*c^3/81 + 1676*b^4*c^4/81 + 1600*b^3*c^5/81 + 1010*b^2*c^6/81 + 280*b*c^7/81 + 32*c^8/81 := by
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

end Lean92.Evan_chen_P18


theorem P18 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 3) : 6 ≤ 18 / ((3 - c) * (4 - c)) + 18 / ((3 - b) * (4 - b)) + 18 / ((3 - a) * (4 - a)) + 2 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  exact @Lean92.Evan_chen_P18.P18 a b c ha hb hc h

#print axioms P18
