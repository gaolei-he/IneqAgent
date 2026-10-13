import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem real_p7' (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h : a + b + c = 3) : (a^2 - a * b + b^2) * (b^2 - b * c + c^2) * (c^2 - c * a + a^2) + 11 * a * b * c ≤ 12 := by
  rw [← sub_nonneg]
  field_simp
  ring_nf
  have hQ : a + b + c = 3 := by nlinarith [h]
  have hQunit : a/3 + b/3 + c/3 = 1 := by nlinarith [hQ]
  suffices hH :
      0 ≤ -a^4*b^2 + a^4*b*c - a^4*c^2 + a^3*b^3 + a^3*c^3 - a^2*b^4 - a^2*b^2*c^2 - a^2*c^4 + a*b^4*c + a*b*c^4 - 11*a*b*c*(a/3 + b/3 + c/3)^3 - b^4*c^2 + b^3*c^3 - b^2*c^4 + 12*(a/3 + b/3 + c/3)^6 by
    convert hH using 1
    try rw [hQunit]
    try rw [hQ]
    ring_nf
  ring_nf
  clear h hQ hQunit
  have hDS_class_1 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ 4*a^6/243 + 8*a^5*b/81 + 8*a^5*c/81 - 61*a^4*b^2/81 + 88*a^4*b*c/81 - 61*a^4*c^2/81 + 323*a^3*b^3/243 - 19*a^3*b^2*c/81 - 19*a^3*b*c^2/81 + 323*a^3*c^3/243 - 61*a^2*b^4/81 - 19*a^2*b^3*c/81 - 53*a^2*b^2*c^2/27 - 19*a^2*b*c^3/81 - 61*a^2*c^4/81 + 8*a*b^5/81 + 88*a*b^4*c/81 - 19*a*b^3*c^2/81 - 19*a*b^2*c^3/81 + 88*a*b*c^4/81 + 8*a*c^5/81 + 4*b^6/243 + 8*b^5*c/81 - 61*b^4*c^2/81 + 323*b^3*c^3/243 - 61*b^2*c^4/81 + 8*b*c^5/81 + 4*c^6/243 := by
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
    have h_t1_2_t1_1 := le_total t1_2 t1_1
    rcases h_t1_2_t1_1 with h_t1_2_t1_1 | h_t1_1_t1_2
    ·
      have h_t1_3_t1_2 := le_total t1_3 t1_2
      rcases h_t1_3_t1_2 with h_t1_3_t1_2 | h_t1_2_t1_3
      ·
        set t2_1 := t1_3
        set t2_2 := t1_2 - t1_3
        set t2_3 := t1_1 - t1_2
        have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_3_nonneg
        have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
        have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
        have h_t1_2_eq : t1_2 = t2_1 + t2_2 := by
          dsimp [t2_1, t2_2]
          ring_nf
        have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 := by
          dsimp [t2_1, t2_2, t2_3]
          ring_nf
        rw [h_t1_2_eq, h_t1_1_eq]
        ring_nf
        positivity
      ·
        have h_t1_3_t1_1 := le_total t1_3 t1_1
        rcases h_t1_3_t1_1 with h_t1_3_t1_1 | h_t1_1_t1_3
        ·
          set t2_1 := t1_2
          set t2_2 := t1_3 - t1_2
          set t2_3 := t1_1 - t1_3
          have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_2_nonneg
          have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
          have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
          have h_t1_3_eq : t1_3 = t2_1 + t2_2 := by
            dsimp [t2_1, t2_2]
            ring_nf
          have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 := by
            dsimp [t2_1, t2_2, t2_3]
            ring_nf
          rw [h_t1_3_eq, h_t1_1_eq]
          ring_nf
          positivity
        ·
          set t2_1 := t1_2
          set t2_2 := t1_1 - t1_2
          set t2_3 := t1_3 - t1_1
          have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_2_nonneg
          have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
          have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
          have h_t1_1_eq : t1_1 = t2_1 + t2_2 := by
            dsimp [t2_1, t2_2]
            ring_nf
          have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 := by
            dsimp [t2_1, t2_2, t2_3]
            ring_nf
          rw [h_t1_1_eq, h_t1_3_eq]
          ring_nf
          positivity
    ·
      have h_t1_3_t1_1 := le_total t1_3 t1_1
      rcases h_t1_3_t1_1 with h_t1_3_t1_1 | h_t1_1_t1_3
      ·
        set t2_1 := t1_3
        set t2_2 := t1_1 - t1_3
        set t2_3 := t1_2 - t1_1
        have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_3_nonneg
        have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
        have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
        have h_t1_1_eq : t1_1 = t2_1 + t2_2 := by
          dsimp [t2_1, t2_2]
          ring_nf
        have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 := by
          dsimp [t2_1, t2_2, t2_3]
          ring_nf
        rw [h_t1_1_eq, h_t1_2_eq]
        ring_nf
        positivity
      ·
        have h_t1_3_t1_2 := le_total t1_3 t1_2
        rcases h_t1_3_t1_2 with h_t1_3_t1_2 | h_t1_2_t1_3
        ·
          set t2_1 := t1_1
          set t2_2 := t1_3 - t1_1
          set t2_3 := t1_2 - t1_3
          have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_1_nonneg
          have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
          have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
          have h_t1_3_eq : t1_3 = t2_1 + t2_2 := by
            dsimp [t2_1, t2_2]
            ring_nf
          have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 := by
            dsimp [t2_1, t2_2, t2_3]
            ring_nf
          rw [h_t1_3_eq, h_t1_2_eq]
          ring_nf
          positivity
        ·
          set t2_1 := t1_1
          set t2_2 := t1_2 - t1_1
          set t2_3 := t1_3 - t1_2
          have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_1_nonneg
          have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
          have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
          have h_t1_2_eq : t1_2 = t2_1 + t2_2 := by
            dsimp [t2_1, t2_2]
            ring_nf
          have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 := by
            dsimp [t2_1, t2_2, t2_3]
            ring_nf
          rw [h_t1_2_eq, h_t1_3_eq]
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



theorem real_p7 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (h : a + b + c = 3) : (a^2 - a * b + b^2) * (b^2 - b * c + c^2) * (c^2 - c * a + a^2) + 11 * a * b * c ≤ 12 := by
  exact @real_p7' a b c ha hb hc h
