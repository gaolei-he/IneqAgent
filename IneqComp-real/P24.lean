import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem real_p24' (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : c / a + a / (b + c) + b / c ≥ 2 := by
  rw [ge_iff_le]
  rw [← sub_nonneg]
  have hden1_pos : 0 < b + c := by
    first
    | positivity
    | nlinarith [ha, hb, hc]
  have hden1_ne : b + c ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < c := by
    first
    | positivity
    | nlinarith [ha, hb, hc]
  have hden2_ne : c ≠ 0 := ne_of_gt hden2_pos
  have hden3_pos : 0 < a := by
    first
    | positivity
    | nlinarith [ha, hb, hc]
  have hden3_ne : a ≠ 0 := ne_of_gt hden3_pos
  field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm, hden1_pos, hden2_pos, hden3_pos]
  ring_nf
  clear hden1_pos hden2_pos hden3_pos hden1_ne hden2_ne hden3_ne
  have hDS_class_1 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ a^2*c + a*b^2 - a*b*c - 2*a*c^2 + b*c^2 + c^3 := by
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
  have hDS_class_2 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ a^2*b - 2*a*b^2 - a*b*c + a*c^2 + b^3 + b^2*c := by
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
  have hDS_class_3 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ a^2*b - a*b*c + a*c^2 + b^2*c - 2*b*c^2 + c^3 := by
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
  have hDS_class_4 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ a^3 - 2*a^2*b + a^2*c + a*b^2 - a*b*c + b*c^2 := by
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
  have hDS_class_5 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ a^2*c + a*b^2 - a*b*c + b^3 - 2*b^2*c + b*c^2 := by
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
  have hDS_class_6 : ∀ a b c : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → a ≤ b ∧ b ≤ c → 0 ≤ a^3 + a^2*b - 2*a^2*c - a*b*c + a*c^2 + b^2*c := by
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
      have hcert := hDS_class_6 c b a (by positivity) (by positivity) (by positivity) hs
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
        have hcert := hDS_class_5 b c a (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring_nf
      ·
        have hs : b ≤ a ∧ a ≤ c := by
          constructor
          · linarith
          ·
            linarith
        have hcert := hDS_class_3 b a c (by positivity) (by positivity) (by positivity) hs
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
      have hcert := hDS_class_4 c a b (by positivity) (by positivity) (by positivity) hs
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



theorem real_p24 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : c / a + a / (b + c) + b / c ≥ 2 := by
  exact @real_p24' a b c ha hb hc
