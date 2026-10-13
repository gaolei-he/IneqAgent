import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem P26' {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 3) : (a / (2 * a ^ 2 + a + 1) + b / (2 * b ^ 2 + b + 1) + c / (2 * c ^ 2 + c + 1)) ≤ 3 / 4 := by
  rw [← sub_nonneg]
  have hden1_pos : 0 < a*(2*a + 1) + 1 := by
    nlinarith [sq_nonneg (a + 1/4)]
  have hden1_ne : a*(2*a + 1) + 1 ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < b*(2*b + 1) + 1 := by
    nlinarith [sq_nonneg (b + 1/4)]
  have hden2_ne : b*(2*b + 1) + 1 ≠ 0 := ne_of_gt hden2_pos
  have hden3_pos : 0 < c*(2*c + 1) + 1 := by
    nlinarith [sq_nonneg (c + 1/4)]
  have hden3_ne : c*(2*c + 1) + 1 ≠ 0 := ne_of_gt hden3_pos
  field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm, hden1_pos, hden2_pos, hden3_pos, hden1_ne, hden2_ne, hden3_ne]
  ring_nf
  have hQ : a + b + c = 3 := by nlinarith [h]
  have hQunit : a/3 + b/3 + c/3 = 1 := by nlinarith [hQ]
  suffices hH :
      0 ≤ 24*a^2*b^2*c^2 - 4*a^2*b^2*c*(a/3 + b/3 + c/3) + 12*a^2*b^2*(a/3 + b/3 + c/3)^2 - 4*a^2*b*c^2*(a/3 + b/3 + c/3) - 10*a^2*b*c*(a/3 + b/3 + c/3)^2 - 2*a^2*b*(a/3 + b/3 + c/3)^3 + 12*a^2*c^2*(a/3 + b/3 + c/3)^2 - 2*a^2*c*(a/3 + b/3 + c/3)^3 + 6*a^2*(a/3 + b/3 + c/3)^4 - 4*a*b^2*c^2*(a/3 + b/3 + c/3) - 10*a*b^2*c*(a/3 + b/3 + c/3)^2 - 2*a*b^2*(a/3 + b/3 + c/3)^3 - 10*a*b*c^2*(a/3 + b/3 + c/3)^2 - 9*a*b*c*(a/3 + b/3 + c/3)^3 - 5*a*b*(a/3 + b/3 + c/3)^4 - 2*a*c^2*(a/3 + b/3 + c/3)^3 - 5*a*c*(a/3 + b/3 + c/3)^4 - a*(a/3 + b/3 + c/3)^5 + 12*b^2*c^2*(a/3 + b/3 + c/3)^2 - 2*b^2*c*(a/3 + b/3 + c/3)^3 + 6*b^2*(a/3 + b/3 + c/3)^4 - 2*b*c^2*(a/3 + b/3 + c/3)^3 - 5*b*c*(a/3 + b/3 + c/3)^4 - b*(a/3 + b/3 + c/3)^5 + 6*c^2*(a/3 + b/3 + c/3)^4 - c*(a/3 + b/3 + c/3)^5 + 3*(a/3 + b/3 + c/3)^6 by
    convert hH using 1
    try rw [hQunit]
    try rw [hQ]
    ring_nf
  ring_nf
  clear h hQ hQunit
  clear hden1_pos hden2_pos hden3_pos hden1_ne hden2_ne hden3_ne
  have hDS_class_1 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ 2*a^6/27 + 13*a^5*b/81 + 13*a^5*c/81 + 106*a^4*b^2/81 - 14*a^4*b*c/9 + 106*a^4*c^2/81 + 22*a^3*b^3/9 - 335*a^3*b^2*c/81 - 335*a^3*b*c^2/81 + 22*a^3*c^3/9 + 106*a^2*b^4/81 - 335*a^2*b^3*c/81 + 118*a^2*b^2*c^2/9 - 335*a^2*b*c^3/81 + 106*a^2*c^4/81 + 13*a*b^5/81 - 14*a*b^4*c/9 - 335*a*b^3*c^2/81 - 335*a*b^2*c^3/81 - 14*a*b*c^4/9 + 13*a*c^5/81 + 2*b^6/27 + 13*b^5*c/81 + 106*b^4*c^2/81 + 22*b^3*c^3/9 + 106*b^2*c^4/81 + 13*b*c^5/81 + 2*c^6/27 := by
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



theorem P26 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 3) : (a / (2 * a ^ 2 + a + 1) + b / (2 * b ^ 2 + b + 1) + c / (2 * c ^ 2 + c + 1)) ≤ 3 / 4 := by
  exact @P26' a b c ha hb hc h
