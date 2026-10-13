import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem P31' {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (3 / 2) * (a ^ 2 + b ^ 2 + c ^ 2) ≤ (a ^ 3 + 5 * b ^ 3) / (3 * a + b) + (b ^ 3 + 5 * c ^ 3) / (3 * b + c) + (c ^ 3 + 5 * a ^ 3) / (3 * c + a) := by
  rw [← sub_nonneg]
  have hden1_pos : 0 < 3*a + b := by
    first
    | positivity
    | nlinarith [ha, hb, hc]
  have hden1_ne : 3*a + b ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < 3*b + c := by
    first
    | positivity
    | nlinarith [ha, hb, hc]
  have hden2_ne : 3*b + c ≠ 0 := ne_of_gt hden2_pos
  have hden3_pos : 0 < a + 3*c := by
    first
    | positivity
    | nlinarith [ha, hb, hc]
  have hden3_ne : a + 3*c ≠ 0 := ne_of_gt hden3_pos
  field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm, hden1_pos, hden2_pos, hden3_pos]
  ring_nf
  clear hden1_pos hden2_pos hden3_pos hden1_ne hden2_ne hden3_ne
  have hDS_class_1 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ 69*a^4*b + 23*a^4*c + 21*a^3*b^2 - 56*a^3*b*c - 21*a^3*c^2 - 21*a^2*b^3 - 36*a^2*b^2*c - 36*a^2*b*c^2 + 21*a^2*c^3 + 23*a*b^4 - 56*a*b^3*c - 36*a*b^2*c^2 - 56*a*b*c^3 + 69*a*c^4 + 69*b^4*c + 21*b^3*c^2 - 21*b^2*c^3 + 23*b*c^4 := by
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
  have hDS_class_2 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ 23*a^4*b + 69*a^4*c - 21*a^3*b^2 - 56*a^3*b*c + 21*a^3*c^2 + 21*a^2*b^3 - 36*a^2*b^2*c - 36*a^2*b*c^2 - 21*a^2*c^3 + 69*a*b^4 - 56*a*b^3*c - 36*a*b^2*c^2 - 56*a*b*c^3 + 23*a*c^4 + 23*b^4*c - 21*b^3*c^2 + 21*b^2*c^3 + 69*b*c^4 := by
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
      have hcert := hDS_class_2 c b a (by positivity) (by positivity) (by positivity) hs
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
        have hcert := hDS_class_2 b a c (by positivity) (by positivity) (by positivity) hs
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
        have hcert := hDS_class_2 a c b (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf
      ·
        have hs : a ≤ b ∧ b ≤ c := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_1 a b c (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf



theorem P31 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : (3 / 2) * (a ^ 2 + b ^ 2 + c ^ 2) ≤ (a ^ 3 + 5 * b ^ 3) / (3 * a + b) + (b ^ 3 + 5 * c ^ 3) / (3 * b + c) + (c ^ 3 + 5 * a ^ 3) / (3 * c + a) := by
  exact @P31' a b c ha hb hc
