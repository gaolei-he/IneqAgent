import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


private theorem private_hDS_class_1 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^3*c + a^3*d + a^2*b^2 - a^2*b*d - 2*a^2*c^2 - a^2*c*d + a^2*d^2 + a*b^3 - a*b^2*c - a*b^2*d - a*b*c^2 + a*c^3 - a*c*d^2 + b^3*d + b^2*c^2 - 2*b^2*d^2 + b*c^3 - b*c^2*d - b*c*d^2 + b*d^3 + c^2*d^2 + c*d^3 := by
  intro a b c d h_a_nonneg_base h_b_nonneg_base h_c_nonneg_base h_d_nonneg_base hsort
  have h_a_b : a ≤ b := hsort.1
  have h_b_c : b ≤ c := hsort.2.1
  have h_c_d : c ≤ d := hsort.2.2
  set t1_1 := a
  set t1_2 := b - a
  set t1_3 := c - b
  set t1_4 := d - c
  have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
  have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
  have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
  have h_t1_4_nonneg : t1_4 ≥ 0 := by linarith
  have h_b_eq : b = t1_1 + t1_2 := by
    dsimp [t1_1, t1_2]
    ring_nf
  have h_c_eq : c = t1_1 + t1_2 + t1_3 := by
    dsimp [t1_1, t1_2, t1_3]
    ring_nf
  have h_d_eq : d = t1_1 + t1_2 + t1_3 + t1_4 := by
    dsimp [t1_1, t1_2, t1_3, t1_4]
    ring_nf
  rw [h_b_eq, h_c_eq, h_d_eq]
  suffices hleaf : (0 : ℝ) ≤ 4*t1_1^2*t1_2^2 + 8*t1_1^2*t1_2*t1_3 + 8*t1_1^2*t1_3^2 + 8*t1_1^2*t1_3*t1_4 + 4*t1_1^2*t1_4^2 + 6*t1_1*t1_2^3 + 17*t1_1*t1_2^2*t1_3 + 3*t1_1*t1_2^2*t1_4 + 21*t1_1*t1_2*t1_3^2 + 18*t1_1*t1_2*t1_3*t1_4 + 7*t1_1*t1_2*t1_4^2 + 8*t1_1*t1_3^3 + 13*t1_1*t1_3^2*t1_4 + 9*t1_1*t1_3*t1_4^2 + 2*t1_1*t1_4^3 + 2*t1_2^4 + 7*t1_2^3*t1_3 + 2*t1_2^3*t1_4 + 11*t1_2^2*t1_3^2 + 11*t1_2^2*t1_3*t1_4 + 4*t1_2^2*t1_4^2 + 8*t1_2*t1_3^3 + 15*t1_2*t1_3^2*t1_4 + 10*t1_2*t1_3*t1_4^2 + 2*t1_2*t1_4^3 + 2*t1_3^4 + 5*t1_3^3*t1_4 + 4*t1_3^2*t1_4^2 + t1_3*t1_4^3 by
    convert hleaf using 1 <;> ring
  positivity

private theorem private_hDS_class_2 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^3*c + a^3*d + a^2*b^2 - a^2*b*c + a^2*c^2 - a^2*c*d - 2*a^2*d^2 + a*b^3 - a*b^2*c - a*b^2*d - a*b*d^2 - a*c^2*d + a*d^3 + b^3*c - 2*b^2*c^2 + b^2*d^2 + b*c^3 - b*c^2*d - b*c*d^2 + b*d^3 + c^3*d + c^2*d^2 := by
  intro a b c d h_a_nonneg_base h_b_nonneg_base h_c_nonneg_base h_d_nonneg_base hsort
  have h_a_b : a ≤ b := hsort.1
  have h_b_c : b ≤ c := hsort.2.1
  have h_c_d : c ≤ d := hsort.2.2
  set t1_1 := a
  set t1_2 := b - a
  set t1_3 := c - b
  set t1_4 := d - c
  have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
  have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
  have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
  have h_t1_4_nonneg : t1_4 ≥ 0 := by linarith
  have h_b_eq : b = t1_1 + t1_2 := by
    dsimp [t1_1, t1_2]
    ring_nf
  have h_c_eq : c = t1_1 + t1_2 + t1_3 := by
    dsimp [t1_1, t1_2, t1_3]
    ring_nf
  have h_d_eq : d = t1_1 + t1_2 + t1_3 + t1_4 := by
    dsimp [t1_1, t1_2, t1_3, t1_4]
    ring_nf
  rw [h_b_eq, h_c_eq, h_d_eq]
  suffices hleaf : (0 : ℝ) ≤ 4*t1_1^2*t1_2^2 + 8*t1_1^2*t1_2*t1_3 + 8*t1_1^2*t1_2*t1_4 + 8*t1_1^2*t1_3^2 + 8*t1_1^2*t1_3*t1_4 + 4*t1_1^2*t1_4^2 + 6*t1_1*t1_2^3 + 17*t1_1*t1_2^2*t1_3 + 14*t1_1*t1_2^2*t1_4 + 21*t1_1*t1_2*t1_3^2 + 24*t1_1*t1_2*t1_3*t1_4 + 10*t1_1*t1_2*t1_4^2 + 8*t1_1*t1_3^3 + 11*t1_1*t1_3^2*t1_4 + 7*t1_1*t1_3*t1_4^2 + 2*t1_1*t1_4^3 + 2*t1_2^4 + 7*t1_2^3*t1_3 + 5*t1_2^3*t1_4 + 11*t1_2^2*t1_3^2 + 11*t1_2^2*t1_3*t1_4 + 4*t1_2^2*t1_4^2 + 8*t1_2*t1_3^3 + 9*t1_2*t1_3^2*t1_4 + 4*t1_2*t1_3*t1_4^2 + t1_2*t1_4^3 + 2*t1_3^4 + 3*t1_3^3*t1_4 + t1_3^2*t1_4^2 by
    convert hleaf using 1 <;> ring
  positivity

private theorem private_hDS_class_3 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^3*b + a^3*d - 2*a^2*b^2 - a^2*b*d + a^2*c^2 - a^2*c*d + a^2*d^2 + a*b^3 - a*b^2*c - a*b*c^2 - a*b*d^2 + a*c^3 - a*c^2*d + b^3*c + b^2*c^2 - b^2*c*d + b^2*d^2 - b*c*d^2 + b*d^3 + c^3*d - 2*c^2*d^2 + c*d^3 := by
  intro a b c d h_a_nonneg_base h_b_nonneg_base h_c_nonneg_base h_d_nonneg_base hsort
  have h_a_b : a ≤ b := hsort.1
  have h_b_c : b ≤ c := hsort.2.1
  have h_c_d : c ≤ d := hsort.2.2
  set t1_1 := a
  set t1_2 := b - a
  set t1_3 := c - b
  set t1_4 := d - c
  have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
  have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
  have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
  have h_t1_4_nonneg : t1_4 ≥ 0 := by linarith
  have h_b_eq : b = t1_1 + t1_2 := by
    dsimp [t1_1, t1_2]
    ring_nf
  have h_c_eq : c = t1_1 + t1_2 + t1_3 := by
    dsimp [t1_1, t1_2, t1_3]
    ring_nf
  have h_d_eq : d = t1_1 + t1_2 + t1_3 + t1_4 := by
    dsimp [t1_1, t1_2, t1_3, t1_4]
    ring_nf
  rw [h_b_eq, h_c_eq, h_d_eq]
  suffices hleaf : (0 : ℝ) ≤ 4*t1_1^2*t1_2^2 + 4*t1_1^2*t1_4^2 + 6*t1_1*t1_2^3 + 4*t1_1*t1_2^2*t1_3 + 3*t1_1*t1_2^2*t1_4 + 2*t1_1*t1_2*t1_3*t1_4 + 7*t1_1*t1_2*t1_4^2 + 4*t1_1*t1_3*t1_4^2 + 2*t1_1*t1_4^3 + 2*t1_2^4 + 3*t1_2^3*t1_3 + 2*t1_2^3*t1_4 + t1_2^2*t1_3^2 + 3*t1_2^2*t1_3*t1_4 + 4*t1_2^2*t1_4^2 + t1_2*t1_3^2*t1_4 + 4*t1_2*t1_3*t1_4^2 + 2*t1_2*t1_4^3 + t1_3^2*t1_4^2 + t1_3*t1_4^3 by
    convert hleaf using 1 <;> ring
  positivity

private theorem private_hDS_class_4 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^3*b + a^3*d + a^2*b^2 - a^2*b*c - a^2*b*d + a^2*c^2 - 2*a^2*d^2 - a*b^2*d - a*b*c^2 + a*c^3 - a*c^2*d - a*c*d^2 + a*d^3 + b^3*c + b^3*d - 2*b^2*c^2 - b^2*c*d + b^2*d^2 + b*c^3 - b*c*d^2 + c^2*d^2 + c*d^3 := by
  intro a b c d h_a_nonneg_base h_b_nonneg_base h_c_nonneg_base h_d_nonneg_base hsort
  have h_a_b : a ≤ b := hsort.1
  have h_b_c : b ≤ c := hsort.2.1
  have h_c_d : c ≤ d := hsort.2.2
  set t1_1 := a
  set t1_2 := b - a
  set t1_3 := c - b
  set t1_4 := d - c
  have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
  have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
  have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
  have h_t1_4_nonneg : t1_4 ≥ 0 := by linarith
  have h_b_eq : b = t1_1 + t1_2 := by
    dsimp [t1_1, t1_2]
    ring_nf
  have h_c_eq : c = t1_1 + t1_2 + t1_3 := by
    dsimp [t1_1, t1_2, t1_3]
    ring_nf
  have h_d_eq : d = t1_1 + t1_2 + t1_3 + t1_4 := by
    dsimp [t1_1, t1_2, t1_3, t1_4]
    ring_nf
  rw [h_b_eq, h_c_eq, h_d_eq]
  suffices hleaf : (0 : ℝ) ≤ 4*t1_1^2*t1_2^2 + 8*t1_1^2*t1_2*t1_3 + 8*t1_1^2*t1_2*t1_4 + 8*t1_1^2*t1_3^2 + 8*t1_1^2*t1_3*t1_4 + 4*t1_1^2*t1_4^2 + 6*t1_1*t1_2^3 + 15*t1_1*t1_2^2*t1_3 + 14*t1_1*t1_2^2*t1_4 + 19*t1_1*t1_2*t1_3^2 + 24*t1_1*t1_2*t1_3*t1_4 + 10*t1_1*t1_2*t1_4^2 + 8*t1_1*t1_3^3 + 13*t1_1*t1_3^2*t1_4 + 9*t1_1*t1_3*t1_4^2 + 2*t1_1*t1_4^3 + 2*t1_2^4 + 6*t1_2^3*t1_3 + 5*t1_2^3*t1_4 + 10*t1_2^2*t1_3^2 + 12*t1_2^2*t1_3*t1_4 + 4*t1_2^2*t1_4^2 + 8*t1_2*t1_3^3 + 13*t1_2*t1_3^2*t1_4 + 7*t1_2*t1_3*t1_4^2 + t1_2*t1_4^3 + 2*t1_3^4 + 5*t1_3^3*t1_4 + 4*t1_3^2*t1_4^2 + t1_3*t1_4^3 by
    convert hleaf using 1 <;> ring
  positivity

private theorem private_hDS_class_5 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^3*b + a^3*c - 2*a^2*b^2 - a^2*b*c + a^2*c^2 - a^2*c*d + a^2*d^2 + a*b^3 - a*b^2*d - a*b*c^2 - a*b*d^2 - a*c*d^2 + a*d^3 + b^3*d + b^2*c^2 - b^2*c*d + b^2*d^2 + b*c^3 - b*c^2*d + c^3*d - 2*c^2*d^2 + c*d^3 := by
  intro a b c d h_a_nonneg_base h_b_nonneg_base h_c_nonneg_base h_d_nonneg_base hsort
  have h_a_b : a ≤ b := hsort.1
  have h_b_c : b ≤ c := hsort.2.1
  have h_c_d : c ≤ d := hsort.2.2
  set t1_1 := a
  set t1_2 := b - a
  set t1_3 := c - b
  set t1_4 := d - c
  have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
  have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
  have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
  have h_t1_4_nonneg : t1_4 ≥ 0 := by linarith
  have h_b_eq : b = t1_1 + t1_2 := by
    dsimp [t1_1, t1_2]
    ring_nf
  have h_c_eq : c = t1_1 + t1_2 + t1_3 := by
    dsimp [t1_1, t1_2, t1_3]
    ring_nf
  have h_d_eq : d = t1_1 + t1_2 + t1_3 + t1_4 := by
    dsimp [t1_1, t1_2, t1_3, t1_4]
    ring_nf
  rw [h_b_eq, h_c_eq, h_d_eq]
  suffices hleaf : (0 : ℝ) ≤ 4*t1_1^2*t1_2^2 + 4*t1_1^2*t1_4^2 + 6*t1_1*t1_2^3 + 4*t1_1*t1_2^2*t1_3 + t1_1*t1_2^2*t1_4 - 2*t1_1*t1_2*t1_3*t1_4 + 5*t1_1*t1_2*t1_4^2 + 4*t1_1*t1_3*t1_4^2 + 2*t1_1*t1_4^3 + 2*t1_2^4 + 3*t1_2^3*t1_3 + t1_2^3*t1_4 + t1_2^2*t1_3^2 - t1_2^2*t1_3*t1_4 + 2*t1_2^2*t1_4^2 - t1_2*t1_3^2*t1_4 + 2*t1_2*t1_3*t1_4^2 + t1_2*t1_4^3 + t1_3^2*t1_4^2 + t1_3*t1_4^3 by
    convert hleaf using 1 <;> ring
  have h_t1_2_t1_1 := le_total t1_2 t1_1
  rcases h_t1_2_t1_1 with h_t1_2_t1_1 | h_t1_1_t1_2
  ·
    have h_t1_3_t1_2 := le_total t1_3 t1_2
    rcases h_t1_3_t1_2 with h_t1_3_t1_2 | h_t1_2_t1_3
    ·
      have h_t1_4_t1_3 := le_total t1_4 t1_3
      rcases h_t1_4_t1_3 with h_t1_4_t1_3 | h_t1_3_t1_4
      ·
        set t2_1 := t1_4
        set t2_2 := t1_3 - t1_4
        set t2_3 := t1_2 - t1_3
        set t2_4 := t1_1 - t1_2
        have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_4_nonneg
        have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
        have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
        have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
        have h_t1_3_eq : t1_3 = t2_1 + t2_2 := by
          dsimp [t2_1, t2_2]
          ring_nf
        have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 := by
          dsimp [t2_1, t2_2, t2_3]
          ring_nf
        have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 + t2_4 := by
          dsimp [t2_1, t2_2, t2_3, t2_4]
          ring_nf
        rw [h_t1_3_eq, h_t1_2_eq, h_t1_1_eq]
        suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 114*t2_1^3*t2_2 + 101*t2_1^3*t2_3 + 36*t2_1^3*t2_4 + 132*t2_1^2*t2_2^2 + 239*t2_1^2*t2_2*t2_3 + 69*t2_1^2*t2_2*t2_4 + 108*t2_1^2*t2_3^2 + 63*t2_1^2*t2_3*t2_4 + 8*t2_1^2*t2_4^2 + 78*t2_1*t2_2^3 + 212*t2_1*t2_2^2*t2_3 + 53*t2_1*t2_2^2*t2_4 + 191*t2_1*t2_2*t2_3^2 + 100*t2_1*t2_2*t2_3*t2_4 + 8*t2_1*t2_2*t2_4^2 + 57*t2_1*t2_3^3 + 47*t2_1*t2_3^2*t2_4 + 8*t2_1*t2_3*t2_4^2 + 20*t2_2^4 + 71*t2_2^3*t2_3 + 18*t2_2^3*t2_4 + 94*t2_2^2*t2_3^2 + 50*t2_2^2*t2_3*t2_4 + 4*t2_2^2*t2_4^2 + 55*t2_2*t2_3^3 + 46*t2_2*t2_3^2*t2_4 + 8*t2_2*t2_3*t2_4^2 + 12*t2_3^4 + 14*t2_3^3*t2_4 + 4*t2_3^2*t2_4^2 by
          convert hleaf using 1 <;> ring
        positivity
      ·
        have h_t1_4_t1_2 := le_total t1_4 t1_2
        rcases h_t1_4_t1_2 with h_t1_4_t1_2 | h_t1_2_t1_4
        ·
          set t2_1 := t1_3
          set t2_2 := t1_4 - t1_3
          set t2_3 := t1_2 - t1_4
          set t2_4 := t1_1 - t1_2
          have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_3_nonneg
          have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
          have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
          have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
          have h_t1_4_eq : t1_4 = t2_1 + t2_2 := by
            dsimp [t2_1, t2_2]
            ring_nf
          have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 := by
            dsimp [t2_1, t2_2, t2_3]
            ring_nf
          have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 + t2_4 := by
            dsimp [t2_1, t2_2, t2_3, t2_4]
            ring_nf
          rw [h_t1_4_eq, h_t1_2_eq, h_t1_1_eq]
          suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 147*t2_1^3*t2_2 + 101*t2_1^3*t2_3 + 36*t2_1^3*t2_4 + 202*t2_1^2*t2_2^2 + 280*t2_1^2*t2_2*t2_3 + 102*t2_1^2*t2_2*t2_4 + 108*t2_1^2*t2_3^2 + 63*t2_1^2*t2_3*t2_4 + 8*t2_1^2*t2_4^2 + 123*t2_1*t2_2^3 + 258*t2_1*t2_2^2*t2_3 + 96*t2_1*t2_2^2*t2_4 + 196*t2_1*t2_2*t2_3^2 + 120*t2_1*t2_2*t2_3*t2_4 + 16*t2_1*t2_2*t2_4^2 + 57*t2_1*t2_3^3 + 47*t2_1*t2_3^2*t2_4 + 8*t2_1*t2_3*t2_4^2 + 28*t2_2^4 + 79*t2_2^3*t2_3 + 30*t2_2^3*t2_4 + 89*t2_2^2*t2_3^2 + 57*t2_2^2*t2_3*t2_4 + 8*t2_2^2*t2_4^2 + 50*t2_2*t2_3^3 + 43*t2_2*t2_3^2*t2_4 + 8*t2_2*t2_3*t2_4^2 + 12*t2_3^4 + 14*t2_3^3*t2_4 + 4*t2_3^2*t2_4^2 by
            convert hleaf using 1 <;> ring
          positivity
        ·
          have h_t1_4_t1_1 := le_total t1_4 t1_1
          rcases h_t1_4_t1_1 with h_t1_4_t1_1 | h_t1_1_t1_4
          ·
            set t2_1 := t1_3
            set t2_2 := t1_2 - t1_3
            set t2_3 := t1_4 - t1_2
            set t2_4 := t1_1 - t1_4
            have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_3_nonneg
            have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
            have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
            have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
            have h_t1_2_eq : t1_2 = t2_1 + t2_2 := by
              dsimp [t2_1, t2_2]
              ring_nf
            have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 := by
              dsimp [t2_1, t2_2, t2_3]
              ring_nf
            have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 + t2_4 := by
              dsimp [t2_1, t2_2, t2_3, t2_4]
              ring_nf
            rw [h_t1_2_eq, h_t1_4_eq, h_t1_1_eq]
            suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 147*t2_1^3*t2_2 + 82*t2_1^3*t2_3 + 36*t2_1^3*t2_4 + 202*t2_1^2*t2_2^2 + 226*t2_1^2*t2_2*t2_3 + 102*t2_1^2*t2_2*t2_4 + 77*t2_1^2*t2_3^2 + 55*t2_1^2*t2_3*t2_4 + 8*t2_1^2*t2_4^2 + 123*t2_1*t2_2^3 + 207*t2_1*t2_2^2*t2_3 + 96*t2_1*t2_2^2*t2_4 + 137*t2_1*t2_2*t2_3^2 + 104*t2_1*t2_2*t2_3*t2_4 + 16*t2_1*t2_2*t2_4^2 + 35*t2_1*t2_3^3 + 39*t2_1*t2_3^2*t2_4 + 8*t2_1*t2_3*t2_4^2 + 28*t2_2^4 + 63*t2_2^3*t2_3 + 30*t2_2^3*t2_4 + 61*t2_2^2*t2_3^2 + 49*t2_2^2*t2_3*t2_4 + 8*t2_2^2*t2_4^2 + 30*t2_2*t2_3^3 + 35*t2_2*t2_3^2*t2_4 + 8*t2_2*t2_3*t2_4^2 + 6*t2_3^4 + 10*t2_3^3*t2_4 + 4*t2_3^2*t2_4^2 by
              convert hleaf using 1 <;> ring
            positivity
          ·
            set t2_1 := t1_3
            set t2_2 := t1_2 - t1_3
            set t2_3 := t1_1 - t1_2
            set t2_4 := t1_4 - t1_1
            have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_3_nonneg
            have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
            have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
            have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
            have h_t1_2_eq : t1_2 = t2_1 + t2_2 := by
              dsimp [t2_1, t2_2]
              ring_nf
            have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 := by
              dsimp [t2_1, t2_2, t2_3]
              ring_nf
            have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 + t2_4 := by
              dsimp [t2_1, t2_2, t2_3, t2_4]
              ring_nf
            rw [h_t1_2_eq, h_t1_1_eq, h_t1_4_eq]
            suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 147*t2_1^3*t2_2 + 82*t2_1^3*t2_3 + 46*t2_1^3*t2_4 + 202*t2_1^2*t2_2^2 + 226*t2_1^2*t2_2*t2_3 + 124*t2_1^2*t2_2*t2_4 + 77*t2_1^2*t2_3^2 + 99*t2_1^2*t2_3*t2_4 + 30*t2_1^2*t2_4^2 + 123*t2_1*t2_2^3 + 207*t2_1*t2_2^2*t2_3 + 111*t2_1*t2_2^2*t2_4 + 137*t2_1*t2_2*t2_3^2 + 170*t2_1*t2_2*t2_3*t2_4 + 49*t2_1*t2_2*t2_4^2 + 35*t2_1*t2_3^3 + 66*t2_1*t2_3^2*t2_4 + 35*t2_1*t2_3*t2_4^2 + 4*t2_1*t2_4^3 + 28*t2_2^4 + 63*t2_2^3*t2_3 + 33*t2_2^3*t2_4 + 61*t2_2^2*t2_3^2 + 73*t2_2^2*t2_3*t2_4 + 20*t2_2^2*t2_4^2 + 30*t2_2*t2_3^3 + 55*t2_2*t2_3^2*t2_4 + 28*t2_2*t2_3*t2_4^2 + 3*t2_2*t2_4^3 + 6*t2_3^4 + 14*t2_3^3*t2_4 + 10*t2_3^2*t2_4^2 + 2*t2_3*t2_4^3 by
              convert hleaf using 1 <;> ring
            positivity
    ·
      have h_t1_3_t1_1 := le_total t1_3 t1_1
      rcases h_t1_3_t1_1 with h_t1_3_t1_1 | h_t1_1_t1_3
      ·
        have h_t1_4_t1_2 := le_total t1_4 t1_2
        rcases h_t1_4_t1_2 with h_t1_4_t1_2 | h_t1_2_t1_4
        ·
          set t2_1 := t1_4
          set t2_2 := t1_2 - t1_4
          set t2_3 := t1_3 - t1_2
          set t2_4 := t1_1 - t1_3
          have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_4_nonneg
          have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
          have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
          have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
          have h_t1_2_eq : t1_2 = t2_1 + t2_2 := by
            dsimp [t2_1, t2_2]
            ring_nf
          have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 := by
            dsimp [t2_1, t2_2, t2_3]
            ring_nf
          have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 + t2_4 := by
            dsimp [t2_1, t2_2, t2_3, t2_4]
            ring_nf
          rw [h_t1_2_eq, h_t1_3_eq, h_t1_1_eq]
          suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 114*t2_1^3*t2_2 + 49*t2_1^3*t2_3 + 36*t2_1^3*t2_4 + 132*t2_1^2*t2_2^2 + 94*t2_1^2*t2_2*t2_3 + 69*t2_1^2*t2_2*t2_4 + 15*t2_1^2*t2_3^2 + 22*t2_1^2*t2_3*t2_4 + 8*t2_1^2*t2_4^2 + 78*t2_1*t2_2^3 + 75*t2_1*t2_2^2*t2_3 + 53*t2_1*t2_2^2*t2_4 + 15*t2_1*t2_2*t2_3^2 + 22*t2_1*t2_2*t2_3*t2_4 + 8*t2_1*t2_2*t2_4^2 + 20*t2_2^4 + 27*t2_2^3*t2_3 + 18*t2_2^3*t2_4 + 9*t2_2^2*t2_3^2 + 12*t2_2^2*t2_3*t2_4 + 4*t2_2^2*t2_4^2 by
            convert hleaf using 1 <;> ring
          positivity
        ·
          have h_t1_4_t1_3 := le_total t1_4 t1_3
          rcases h_t1_4_t1_3 with h_t1_4_t1_3 | h_t1_3_t1_4
          ·
            set t2_1 := t1_2
            set t2_2 := t1_4 - t1_2
            set t2_3 := t1_3 - t1_4
            set t2_4 := t1_1 - t1_3
            have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_2_nonneg
            have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
            have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
            have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
            have h_t1_4_eq : t1_4 = t2_1 + t2_2 := by
              dsimp [t2_1, t2_2]
              ring_nf
            have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 := by
              dsimp [t2_1, t2_2, t2_3]
              ring_nf
            have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 + t2_4 := by
              dsimp [t2_1, t2_2, t2_3, t2_4]
              ring_nf
            rw [h_t1_4_eq, h_t1_3_eq, h_t1_1_eq]
            suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 95*t2_1^3*t2_2 + 49*t2_1^3*t2_3 + 36*t2_1^3*t2_4 + 98*t2_1^2*t2_2^2 + 83*t2_1^2*t2_2*t2_3 + 61*t2_1^2*t2_2*t2_4 + 15*t2_1^2*t2_3^2 + 22*t2_1^2*t2_3*t2_4 + 8*t2_1^2*t2_4^2 + 53*t2_1*t2_2^3 + 64*t2_1*t2_2^2*t2_3 + 45*t2_1*t2_2^2*t2_4 + 15*t2_1*t2_2*t2_3^2 + 22*t2_1*t2_2*t2_3*t2_4 + 8*t2_1*t2_2*t2_4^2 + 12*t2_2^4 + 21*t2_2^3*t2_3 + 14*t2_2^3*t2_4 + 9*t2_2^2*t2_3^2 + 12*t2_2^2*t2_3*t2_4 + 4*t2_2^2*t2_4^2 by
              convert hleaf using 1 <;> ring
            positivity
          ·
            have h_t1_4_t1_1 := le_total t1_4 t1_1
            rcases h_t1_4_t1_1 with h_t1_4_t1_1 | h_t1_1_t1_4
            ·
              set t2_1 := t1_2
              set t2_2 := t1_3 - t1_2
              set t2_3 := t1_4 - t1_3
              set t2_4 := t1_1 - t1_4
              have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_2_nonneg
              have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
              have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
              have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
              have h_t1_3_eq : t1_3 = t2_1 + t2_2 := by
                dsimp [t2_1, t2_2]
                ring_nf
              have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 := by
                dsimp [t2_1, t2_2, t2_3]
                ring_nf
              have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 + t2_4 := by
                dsimp [t2_1, t2_2, t2_3, t2_4]
                ring_nf
              rw [h_t1_3_eq, h_t1_4_eq, h_t1_1_eq]
              suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 95*t2_1^3*t2_2 + 82*t2_1^3*t2_3 + 36*t2_1^3*t2_4 + 98*t2_1^2*t2_2^2 + 174*t2_1^2*t2_2*t2_3 + 61*t2_1^2*t2_2*t2_4 + 77*t2_1^2*t2_3^2 + 55*t2_1^2*t2_3*t2_4 + 8*t2_1^2*t2_4^2 + 53*t2_1*t2_2^3 + 140*t2_1*t2_2^2*t2_3 + 45*t2_1*t2_2^2*t2_4 + 122*t2_1*t2_2*t2_3^2 + 84*t2_1*t2_2*t2_3*t2_4 + 8*t2_1*t2_2*t2_4^2 + 35*t2_1*t2_3^3 + 39*t2_1*t2_3^2*t2_4 + 8*t2_1*t2_3*t2_4^2 + 12*t2_2^4 + 41*t2_2^3*t2_3 + 14*t2_2^3*t2_4 + 52*t2_2^2*t2_3^2 + 38*t2_2^2*t2_3*t2_4 + 4*t2_2^2*t2_4^2 + 29*t2_2*t2_3^3 + 34*t2_2*t2_3^2*t2_4 + 8*t2_2*t2_3*t2_4^2 + 6*t2_3^4 + 10*t2_3^3*t2_4 + 4*t2_3^2*t2_4^2 by
                convert hleaf using 1 <;> ring
              positivity
            ·
              set t2_1 := t1_2
              set t2_2 := t1_3 - t1_2
              set t2_3 := t1_1 - t1_3
              set t2_4 := t1_4 - t1_1
              have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_2_nonneg
              have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
              have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
              have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
              have h_t1_3_eq : t1_3 = t2_1 + t2_2 := by
                dsimp [t2_1, t2_2]
                ring_nf
              have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 := by
                dsimp [t2_1, t2_2, t2_3]
                ring_nf
              have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 + t2_4 := by
                dsimp [t2_1, t2_2, t2_3, t2_4]
                ring_nf
              rw [h_t1_3_eq, h_t1_1_eq, h_t1_4_eq]
              suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 95*t2_1^3*t2_2 + 82*t2_1^3*t2_3 + 46*t2_1^3*t2_4 + 98*t2_1^2*t2_2^2 + 174*t2_1^2*t2_2*t2_3 + 113*t2_1^2*t2_2*t2_4 + 77*t2_1^2*t2_3^2 + 99*t2_1^2*t2_3*t2_4 + 30*t2_1^2*t2_4^2 + 53*t2_1*t2_2^3 + 140*t2_1*t2_2^2*t2_3 + 95*t2_1*t2_2^2*t2_4 + 122*t2_1*t2_2*t2_3^2 + 160*t2_1*t2_2*t2_3*t2_4 + 46*t2_1*t2_2*t2_4^2 + 35*t2_1*t2_3^3 + 66*t2_1*t2_3^2*t2_4 + 35*t2_1*t2_3*t2_4^2 + 4*t2_1*t2_4^3 + 12*t2_2^4 + 41*t2_2^3*t2_3 + 27*t2_2^3*t2_4 + 52*t2_2^2*t2_3^2 + 66*t2_2^2*t2_3*t2_4 + 18*t2_2^2*t2_4^2 + 29*t2_2*t2_3^3 + 53*t2_2*t2_3^2*t2_4 + 27*t2_2*t2_3*t2_4^2 + 3*t2_2*t2_4^3 + 6*t2_3^4 + 14*t2_3^3*t2_4 + 10*t2_3^2*t2_4^2 + 2*t2_3*t2_4^3 by
                convert hleaf using 1 <;> ring
              positivity
      ·
        have h_t1_4_t1_2 := le_total t1_4 t1_2
        rcases h_t1_4_t1_2 with h_t1_4_t1_2 | h_t1_2_t1_4
        ·
          set t2_1 := t1_4
          set t2_2 := t1_2 - t1_4
          set t2_3 := t1_1 - t1_2
          set t2_4 := t1_3 - t1_1
          have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_4_nonneg
          have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
          have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
          have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
          have h_t1_2_eq : t1_2 = t2_1 + t2_2 := by
            dsimp [t2_1, t2_2]
            ring_nf
          have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 := by
            dsimp [t2_1, t2_2, t2_3]
            ring_nf
          have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 + t2_4 := by
            dsimp [t2_1, t2_2, t2_3, t2_4]
            ring_nf
          rw [h_t1_2_eq, h_t1_1_eq, h_t1_3_eq]
          suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 114*t2_1^3*t2_2 + 49*t2_1^3*t2_3 + 13*t2_1^3*t2_4 + 132*t2_1^2*t2_2^2 + 94*t2_1^2*t2_2*t2_3 + 25*t2_1^2*t2_2*t2_4 + 15*t2_1^2*t2_3^2 + 8*t2_1^2*t2_3*t2_4 + t2_1^2*t2_4^2 + 78*t2_1*t2_2^3 + 75*t2_1*t2_2^2*t2_3 + 22*t2_1*t2_2^2*t2_4 + 15*t2_1*t2_2*t2_3^2 + 8*t2_1*t2_2*t2_3*t2_4 + t2_1*t2_2*t2_4^2 + 20*t2_2^4 + 27*t2_2^3*t2_3 + 9*t2_2^3*t2_4 + 9*t2_2^2*t2_3^2 + 6*t2_2^2*t2_3*t2_4 + t2_2^2*t2_4^2 by
            convert hleaf using 1 <;> ring
          positivity
        ·
          have h_t1_4_t1_1 := le_total t1_4 t1_1
          rcases h_t1_4_t1_1 with h_t1_4_t1_1 | h_t1_1_t1_4
          ·
            set t2_1 := t1_2
            set t2_2 := t1_4 - t1_2
            set t2_3 := t1_1 - t1_4
            set t2_4 := t1_3 - t1_1
            have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_2_nonneg
            have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
            have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
            have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
            have h_t1_4_eq : t1_4 = t2_1 + t2_2 := by
              dsimp [t2_1, t2_2]
              ring_nf
            have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 := by
              dsimp [t2_1, t2_2, t2_3]
              ring_nf
            have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 + t2_4 := by
              dsimp [t2_1, t2_2, t2_3, t2_4]
              ring_nf
            rw [h_t1_4_eq, h_t1_1_eq, h_t1_3_eq]
            suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 95*t2_1^3*t2_2 + 49*t2_1^3*t2_3 + 13*t2_1^3*t2_4 + 98*t2_1^2*t2_2^2 + 83*t2_1^2*t2_2*t2_3 + 22*t2_1^2*t2_2*t2_4 + 15*t2_1^2*t2_3^2 + 8*t2_1^2*t2_3*t2_4 + t2_1^2*t2_4^2 + 53*t2_1*t2_2^3 + 64*t2_1*t2_2^2*t2_3 + 19*t2_1*t2_2^2*t2_4 + 15*t2_1*t2_2*t2_3^2 + 8*t2_1*t2_2*t2_3*t2_4 + t2_1*t2_2*t2_4^2 + 12*t2_2^4 + 21*t2_2^3*t2_3 + 7*t2_2^3*t2_4 + 9*t2_2^2*t2_3^2 + 6*t2_2^2*t2_3*t2_4 + t2_2^2*t2_4^2 by
              convert hleaf using 1 <;> ring
            positivity
          ·
            have h_t1_4_t1_3 := le_total t1_4 t1_3
            rcases h_t1_4_t1_3 with h_t1_4_t1_3 | h_t1_3_t1_4
            ·
              set t2_1 := t1_2
              set t2_2 := t1_1 - t1_2
              set t2_3 := t1_4 - t1_1
              set t2_4 := t1_3 - t1_4
              have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_2_nonneg
              have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
              have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
              have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
              have h_t1_1_eq : t1_1 = t2_1 + t2_2 := by
                dsimp [t2_1, t2_2]
                ring_nf
              have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 := by
                dsimp [t2_1, t2_2, t2_3]
                ring_nf
              have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 + t2_4 := by
                dsimp [t2_1, t2_2, t2_3, t2_4]
                ring_nf
              rw [h_t1_1_eq, h_t1_4_eq, h_t1_3_eq]
              suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 95*t2_1^3*t2_2 + 59*t2_1^3*t2_3 + 13*t2_1^3*t2_4 + 98*t2_1^2*t2_2^2 + 135*t2_1^2*t2_2*t2_3 + 22*t2_1^2*t2_2*t2_4 + 45*t2_1^2*t2_3^2 + 16*t2_1^2*t2_3*t2_4 + t2_1^2*t2_4^2 + 53*t2_1*t2_2^3 + 114*t2_1*t2_2^2*t2_3 + 19*t2_1*t2_2^2*t2_4 + 77*t2_1*t2_2*t2_3^2 + 32*t2_1*t2_2*t2_3*t2_4 + t2_1*t2_2*t2_4^2 + 16*t2_1*t2_3^3 + 13*t2_1*t2_3^2*t2_4 + t2_1*t2_3*t2_4^2 + 12*t2_2^4 + 34*t2_2^3*t2_3 + 7*t2_2^3*t2_4 + 34*t2_2^2*t2_3^2 + 17*t2_2^2*t2_3*t2_4 + t2_2^2*t2_4^2 + 14*t2_2*t2_3^3 + 13*t2_2*t2_3^2*t2_4 + 2*t2_2*t2_3*t2_4^2 + 2*t2_3^4 + 3*t2_3^3*t2_4 + t2_3^2*t2_4^2 by
                convert hleaf using 1 <;> ring
              positivity
            ·
              set t2_1 := t1_2
              set t2_2 := t1_1 - t1_2
              set t2_3 := t1_3 - t1_1
              set t2_4 := t1_4 - t1_3
              have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_2_nonneg
              have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
              have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
              have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
              have h_t1_1_eq : t1_1 = t2_1 + t2_2 := by
                dsimp [t2_1, t2_2]
                ring_nf
              have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 := by
                dsimp [t2_1, t2_2, t2_3]
                ring_nf
              have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 + t2_4 := by
                dsimp [t2_1, t2_2, t2_3, t2_4]
                ring_nf
              rw [h_t1_1_eq, h_t1_3_eq, h_t1_4_eq]
              suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 95*t2_1^3*t2_2 + 59*t2_1^3*t2_3 + 46*t2_1^3*t2_4 + 98*t2_1^2*t2_2^2 + 135*t2_1^2*t2_2*t2_3 + 113*t2_1^2*t2_2*t2_4 + 45*t2_1^2*t2_3^2 + 74*t2_1^2*t2_3*t2_4 + 30*t2_1^2*t2_4^2 + 53*t2_1*t2_2^3 + 114*t2_1*t2_2^2*t2_3 + 95*t2_1*t2_2^2*t2_4 + 77*t2_1*t2_2*t2_3^2 + 122*t2_1*t2_2*t2_3*t2_4 + 46*t2_1*t2_2*t2_4^2 + 16*t2_1*t2_3^3 + 35*t2_1*t2_3^2*t2_4 + 23*t2_1*t2_3*t2_4^2 + 4*t2_1*t2_4^3 + 12*t2_2^4 + 34*t2_2^3*t2_3 + 27*t2_2^3*t2_4 + 34*t2_2^2*t2_3^2 + 51*t2_2^2*t2_3*t2_4 + 18*t2_2^2*t2_4^2 + 14*t2_2*t2_3^3 + 29*t2_2*t2_3^2*t2_4 + 18*t2_2*t2_3*t2_4^2 + 3*t2_2*t2_4^3 + 2*t2_3^4 + 5*t2_3^3*t2_4 + 4*t2_3^2*t2_4^2 + t2_3*t2_4^3 by
                convert hleaf using 1 <;> ring
              positivity
  ·
    have h_t1_3_t1_1 := le_total t1_3 t1_1
    rcases h_t1_3_t1_1 with h_t1_3_t1_1 | h_t1_1_t1_3
    ·
      have h_t1_4_t1_3 := le_total t1_4 t1_3
      rcases h_t1_4_t1_3 with h_t1_4_t1_3 | h_t1_3_t1_4
      ·
        set t2_1 := t1_4
        set t2_2 := t1_3 - t1_4
        set t2_3 := t1_1 - t1_3
        set t2_4 := t1_2 - t1_1
        have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_4_nonneg
        have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
        have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
        have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
        have h_t1_3_eq : t1_3 = t2_1 + t2_2 := by
          dsimp [t2_1, t2_2]
          ring_nf
        have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 := by
          dsimp [t2_1, t2_2, t2_3]
          ring_nf
        have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 + t2_4 := by
          dsimp [t2_1, t2_2, t2_3, t2_4]
          ring_nf
        rw [h_t1_3_eq, h_t1_1_eq, h_t1_2_eq]
        suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 114*t2_1^3*t2_2 + 101*t2_1^3*t2_3 + 65*t2_1^3*t2_4 + 132*t2_1^2*t2_2^2 + 239*t2_1^2*t2_2*t2_3 + 170*t2_1^2*t2_2*t2_4 + 108*t2_1^2*t2_3^2 + 153*t2_1^2*t2_3*t2_4 + 53*t2_1^2*t2_4^2 + 78*t2_1*t2_2^3 + 212*t2_1*t2_2^2*t2_3 + 159*t2_1*t2_2^2*t2_4 + 191*t2_1*t2_2*t2_3^2 + 282*t2_1*t2_2*t2_3*t2_4 + 99*t2_1*t2_2*t2_4^2 + 57*t2_1*t2_3^3 + 124*t2_1*t2_3^2*t2_4 + 85*t2_1*t2_3*t2_4^2 + 18*t2_1*t2_4^3 + 20*t2_2^4 + 71*t2_2^3*t2_3 + 53*t2_2^3*t2_4 + 94*t2_2^2*t2_3^2 + 138*t2_2^2*t2_3*t2_4 + 48*t2_2^2*t2_4^2 + 55*t2_2*t2_3^3 + 119*t2_2*t2_3^2*t2_4 + 81*t2_2*t2_3*t2_4^2 + 17*t2_2*t2_4^3 + 12*t2_3^4 + 34*t2_3^3*t2_4 + 34*t2_3^2*t2_4^2 + 14*t2_3*t2_4^3 + 2*t2_4^4 by
          convert hleaf using 1 <;> ring
        positivity
      ·
        have h_t1_4_t1_1 := le_total t1_4 t1_1
        rcases h_t1_4_t1_1 with h_t1_4_t1_1 | h_t1_1_t1_4
        ·
          set t2_1 := t1_3
          set t2_2 := t1_4 - t1_3
          set t2_3 := t1_1 - t1_4
          set t2_4 := t1_2 - t1_1
          have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_3_nonneg
          have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
          have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
          have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
          have h_t1_4_eq : t1_4 = t2_1 + t2_2 := by
            dsimp [t2_1, t2_2]
            ring_nf
          have h_t1_1_eq : t1_1 = t2_1 + t2_2 + t2_3 := by
            dsimp [t2_1, t2_2, t2_3]
            ring_nf
          have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 + t2_4 := by
            dsimp [t2_1, t2_2, t2_3, t2_4]
            ring_nf
          rw [h_t1_4_eq, h_t1_1_eq, h_t1_2_eq]
          suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 147*t2_1^3*t2_2 + 101*t2_1^3*t2_3 + 65*t2_1^3*t2_4 + 202*t2_1^2*t2_2^2 + 280*t2_1^2*t2_2*t2_3 + 178*t2_1^2*t2_2*t2_4 + 108*t2_1^2*t2_3^2 + 153*t2_1^2*t2_3*t2_4 + 53*t2_1^2*t2_4^2 + 123*t2_1*t2_2^3 + 258*t2_1*t2_2^2*t2_3 + 162*t2_1*t2_2^2*t2_4 + 196*t2_1*t2_2*t2_3^2 + 272*t2_1*t2_2*t2_3*t2_4 + 92*t2_1*t2_2*t2_4^2 + 57*t2_1*t2_3^3 + 124*t2_1*t2_3^2*t2_4 + 85*t2_1*t2_3*t2_4^2 + 18*t2_1*t2_4^3 + 28*t2_2^4 + 79*t2_2^3*t2_3 + 49*t2_2^3*t2_4 + 89*t2_2^2*t2_3^2 + 121*t2_2^2*t2_3*t2_4 + 40*t2_2^2*t2_4^2 + 50*t2_2*t2_3^3 + 107*t2_2*t2_3^2*t2_4 + 72*t2_2*t2_3*t2_4^2 + 15*t2_2*t2_4^3 + 12*t2_3^4 + 34*t2_3^3*t2_4 + 34*t2_3^2*t2_4^2 + 14*t2_3*t2_4^3 + 2*t2_4^4 by
            convert hleaf using 1 <;> ring
          positivity
        ·
          have h_t1_4_t1_2 := le_total t1_4 t1_2
          rcases h_t1_4_t1_2 with h_t1_4_t1_2 | h_t1_2_t1_4
          ·
            set t2_1 := t1_3
            set t2_2 := t1_1 - t1_3
            set t2_3 := t1_4 - t1_1
            set t2_4 := t1_2 - t1_4
            have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_3_nonneg
            have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
            have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
            have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
            have h_t1_1_eq : t1_1 = t2_1 + t2_2 := by
              dsimp [t2_1, t2_2]
              ring_nf
            have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 := by
              dsimp [t2_1, t2_2, t2_3]
              ring_nf
            have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 + t2_4 := by
              dsimp [t2_1, t2_2, t2_3, t2_4]
              ring_nf
            rw [h_t1_1_eq, h_t1_4_eq, h_t1_2_eq]
            suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 147*t2_1^3*t2_2 + 111*t2_1^3*t2_3 + 65*t2_1^3*t2_4 + 202*t2_1^2*t2_2^2 + 302*t2_1^2*t2_2*t2_3 + 178*t2_1^2*t2_2*t2_4 + 108*t2_1^2*t2_3^2 + 131*t2_1^2*t2_3*t2_4 + 53*t2_1^2*t2_4^2 + 123*t2_1*t2_2^3 + 273*t2_1*t2_2^2*t2_3 + 162*t2_1*t2_2^2*t2_4 + 193*t2_1*t2_2*t2_3^2 + 236*t2_1*t2_2*t2_3*t2_4 + 92*t2_1*t2_2*t2_4^2 + 43*t2_1*t2_3^3 + 82*t2_1*t2_3^2*t2_4 + 61*t2_1*t2_3*t2_4^2 + 18*t2_1*t2_4^3 + 28*t2_2^4 + 82*t2_2^3*t2_3 + 49*t2_2^3*t2_4 + 86*t2_2^2*t2_3^2 + 106*t2_2^2*t2_3*t2_4 + 40*t2_2^2*t2_4^2 + 38*t2_2*t2_3^3 + 73*t2_2*t2_3^2*t2_4 + 53*t2_2*t2_3*t2_4^2 + 15*t2_2*t2_4^3 + 6*t2_3^4 + 16*t2_3^3*t2_4 + 17*t2_3^2*t2_4^2 + 9*t2_3*t2_4^3 + 2*t2_4^4 by
              convert hleaf using 1 <;> ring
            positivity
          ·
            set t2_1 := t1_3
            set t2_2 := t1_1 - t1_3
            set t2_3 := t1_2 - t1_1
            set t2_4 := t1_4 - t1_2
            have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_3_nonneg
            have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
            have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
            have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
            have h_t1_1_eq : t1_1 = t2_1 + t2_2 := by
              dsimp [t2_1, t2_2]
              ring_nf
            have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 := by
              dsimp [t2_1, t2_2, t2_3]
              ring_nf
            have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 + t2_4 := by
              dsimp [t2_1, t2_2, t2_3, t2_4]
              ring_nf
            rw [h_t1_1_eq, h_t1_2_eq, h_t1_4_eq]
            suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 147*t2_1^3*t2_2 + 111*t2_1^3*t2_3 + 46*t2_1^3*t2_4 + 202*t2_1^2*t2_2^2 + 302*t2_1^2*t2_2*t2_3 + 124*t2_1^2*t2_2*t2_4 + 108*t2_1^2*t2_3^2 + 85*t2_1^2*t2_3*t2_4 + 30*t2_1^2*t2_4^2 + 123*t2_1*t2_2^3 + 273*t2_1*t2_2^2*t2_3 + 111*t2_1*t2_2^2*t2_4 + 193*t2_1*t2_2*t2_3^2 + 150*t2_1*t2_2*t2_3*t2_4 + 49*t2_1*t2_2*t2_4^2 + 43*t2_1*t2_3^3 + 47*t2_1*t2_3^2*t2_4 + 26*t2_1*t2_3*t2_4^2 + 4*t2_1*t2_4^3 + 28*t2_2^4 + 82*t2_2^3*t2_3 + 33*t2_2^3*t2_4 + 86*t2_2^2*t2_3^2 + 66*t2_2^2*t2_3*t2_4 + 20*t2_2^2*t2_4^2 + 38*t2_2*t2_3^3 + 41*t2_2*t2_3^2*t2_4 + 21*t2_2*t2_3*t2_4^2 + 3*t2_2*t2_4^3 + 6*t2_3^4 + 8*t2_3^3*t2_4 + 5*t2_3^2*t2_4^2 + t2_3*t2_4^3 by
              convert hleaf using 1 <;> ring
            positivity
    ·
      have h_t1_3_t1_2 := le_total t1_3 t1_2
      rcases h_t1_3_t1_2 with h_t1_3_t1_2 | h_t1_2_t1_3
      ·
        have h_t1_4_t1_1 := le_total t1_4 t1_1
        rcases h_t1_4_t1_1 with h_t1_4_t1_1 | h_t1_1_t1_4
        ·
          set t2_1 := t1_4
          set t2_2 := t1_1 - t1_4
          set t2_3 := t1_3 - t1_1
          set t2_4 := t1_2 - t1_3
          have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_4_nonneg
          have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
          have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
          have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
          have h_t1_1_eq : t1_1 = t2_1 + t2_2 := by
            dsimp [t2_1, t2_2]
            ring_nf
          have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 := by
            dsimp [t2_1, t2_2, t2_3]
            ring_nf
          have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 + t2_4 := by
            dsimp [t2_1, t2_2, t2_3, t2_4]
            ring_nf
          rw [h_t1_1_eq, h_t1_3_eq, h_t1_2_eq]
          suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 114*t2_1^3*t2_2 + 78*t2_1^3*t2_3 + 65*t2_1^3*t2_4 + 132*t2_1^2*t2_2^2 + 195*t2_1^2*t2_2*t2_3 + 170*t2_1^2*t2_2*t2_4 + 71*t2_1^2*t2_3^2 + 123*t2_1^2*t2_3*t2_4 + 53*t2_1^2*t2_4^2 + 78*t2_1*t2_2^3 + 181*t2_1*t2_2^2*t2_3 + 159*t2_1*t2_2^2*t2_4 + 136*t2_1*t2_2*t2_3^2 + 234*t2_1*t2_2*t2_3*t2_4 + 99*t2_1*t2_2*t2_4^2 + 33*t2_1*t2_3^3 + 83*t2_1*t2_3^2*t2_4 + 68*t2_1*t2_3*t2_4^2 + 18*t2_1*t2_4^3 + 20*t2_2^4 + 62*t2_2^3*t2_3 + 53*t2_2^3*t2_4 + 70*t2_2^2*t2_3^2 + 117*t2_2^2*t2_3*t2_4 + 48*t2_2^2*t2_4^2 + 34*t2_2*t2_3^3 + 83*t2_2*t2_3^2*t2_4 + 66*t2_2*t2_3*t2_4^2 + 17*t2_2*t2_4^3 + 6*t2_3^4 + 19*t2_3^3*t2_4 + 22*t2_3^2*t2_4^2 + 11*t2_3*t2_4^3 + 2*t2_4^4 by
            convert hleaf using 1 <;> ring
          positivity
        ·
          have h_t1_4_t1_3 := le_total t1_4 t1_3
          rcases h_t1_4_t1_3 with h_t1_4_t1_3 | h_t1_3_t1_4
          ·
            set t2_1 := t1_1
            set t2_2 := t1_4 - t1_1
            set t2_3 := t1_3 - t1_4
            set t2_4 := t1_2 - t1_3
            have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_1_nonneg
            have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
            have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
            have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
            have h_t1_4_eq : t1_4 = t2_1 + t2_2 := by
              dsimp [t2_1, t2_2]
              ring_nf
            have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 := by
              dsimp [t2_1, t2_2, t2_3]
              ring_nf
            have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 + t2_4 := by
              dsimp [t2_1, t2_2, t2_3, t2_4]
              ring_nf
            rw [h_t1_4_eq, h_t1_3_eq, h_t1_2_eq]
            suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 124*t2_1^3*t2_2 + 78*t2_1^3*t2_3 + 65*t2_1^3*t2_4 + 140*t2_1^2*t2_2^2 + 181*t2_1^2*t2_2*t2_3 + 148*t2_1^2*t2_2*t2_4 + 71*t2_1^2*t2_3^2 + 123*t2_1^2*t2_3*t2_4 + 53*t2_1^2*t2_4^2 + 68*t2_1*t2_2^3 + 136*t2_1*t2_2^2*t2_3 + 109*t2_1*t2_2^2*t2_4 + 105*t2_1*t2_2*t2_3^2 + 178*t2_1*t2_2*t2_3*t2_4 + 75*t2_1*t2_2*t2_4^2 + 33*t2_1*t2_3^3 + 83*t2_1*t2_3^2*t2_4 + 68*t2_1*t2_3*t2_4^2 + 18*t2_1*t2_4^3 + 12*t2_2^4 + 33*t2_2^3*t2_3 + 26*t2_2^3*t2_4 + 38*t2_2^2*t2_3^2 + 63*t2_2^2*t2_3*t2_4 + 26*t2_2^2*t2_4^2 + 23*t2_2*t2_3^3 + 57*t2_2*t2_3^2*t2_4 + 46*t2_2*t2_3*t2_4^2 + 12*t2_2*t2_4^3 + 6*t2_3^4 + 19*t2_3^3*t2_4 + 22*t2_3^2*t2_4^2 + 11*t2_3*t2_4^3 + 2*t2_4^4 by
              convert hleaf using 1 <;> ring
            positivity
          ·
            have h_t1_4_t1_2 := le_total t1_4 t1_2
            rcases h_t1_4_t1_2 with h_t1_4_t1_2 | h_t1_2_t1_4
            ·
              set t2_1 := t1_1
              set t2_2 := t1_3 - t1_1
              set t2_3 := t1_4 - t1_3
              set t2_4 := t1_2 - t1_4
              have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_1_nonneg
              have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
              have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
              have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
              have h_t1_3_eq : t1_3 = t2_1 + t2_2 := by
                dsimp [t2_1, t2_2]
                ring_nf
              have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 := by
                dsimp [t2_1, t2_2, t2_3]
                ring_nf
              have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 + t2_4 := by
                dsimp [t2_1, t2_2, t2_3, t2_4]
                ring_nf
              rw [h_t1_3_eq, h_t1_4_eq, h_t1_2_eq]
              suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 124*t2_1^3*t2_2 + 111*t2_1^3*t2_3 + 65*t2_1^3*t2_4 + 140*t2_1^2*t2_2^2 + 247*t2_1^2*t2_2*t2_3 + 148*t2_1^2*t2_2*t2_4 + 108*t2_1^2*t2_3^2 + 131*t2_1^2*t2_3*t2_4 + 53*t2_1^2*t2_4^2 + 68*t2_1*t2_2^3 + 177*t2_1*t2_2^2*t2_3 + 109*t2_1*t2_2^2*t2_4 + 152*t2_1*t2_2*t2_3^2 + 190*t2_1*t2_2*t2_3*t2_4 + 75*t2_1*t2_2*t2_4^2 + 43*t2_1*t2_3^3 + 82*t2_1*t2_3^2*t2_4 + 61*t2_1*t2_3*t2_4^2 + 18*t2_1*t2_4^3 + 12*t2_2^4 + 41*t2_2^3*t2_3 + 26*t2_2^3*t2_4 + 52*t2_2^2*t2_3^2 + 67*t2_2^2*t2_3*t2_4 + 26*t2_2^2*t2_4^2 + 29*t2_2*t2_3^3 + 57*t2_2*t2_3^2*t2_4 + 42*t2_2*t2_3*t2_4^2 + 12*t2_2*t2_4^3 + 6*t2_3^4 + 16*t2_3^3*t2_4 + 17*t2_3^2*t2_4^2 + 9*t2_3*t2_4^3 + 2*t2_4^4 by
                convert hleaf using 1 <;> ring
              positivity
            ·
              set t2_1 := t1_1
              set t2_2 := t1_3 - t1_1
              set t2_3 := t1_2 - t1_3
              set t2_4 := t1_4 - t1_2
              have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_1_nonneg
              have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
              have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
              have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
              have h_t1_3_eq : t1_3 = t2_1 + t2_2 := by
                dsimp [t2_1, t2_2]
                ring_nf
              have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 := by
                dsimp [t2_1, t2_2, t2_3]
                ring_nf
              have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 + t2_4 := by
                dsimp [t2_1, t2_2, t2_3, t2_4]
                ring_nf
              rw [h_t1_3_eq, h_t1_2_eq, h_t1_4_eq]
              suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 124*t2_1^3*t2_2 + 111*t2_1^3*t2_3 + 46*t2_1^3*t2_4 + 140*t2_1^2*t2_2^2 + 247*t2_1^2*t2_2*t2_3 + 99*t2_1^2*t2_2*t2_4 + 108*t2_1^2*t2_3^2 + 85*t2_1^2*t2_3*t2_4 + 30*t2_1^2*t2_4^2 + 68*t2_1*t2_2^3 + 177*t2_1*t2_2^2*t2_3 + 68*t2_1*t2_2^2*t2_4 + 152*t2_1*t2_2*t2_3^2 + 114*t2_1*t2_2*t2_3*t2_4 + 37*t2_1*t2_2*t2_4^2 + 43*t2_1*t2_3^3 + 47*t2_1*t2_3^2*t2_4 + 26*t2_1*t2_3*t2_4^2 + 4*t2_1*t2_4^3 + 12*t2_2^4 + 41*t2_2^3*t2_3 + 15*t2_2^3*t2_4 + 52*t2_2^2*t2_3^2 + 37*t2_2^2*t2_3*t2_4 + 11*t2_2^2*t2_4^2 + 29*t2_2*t2_3^3 + 30*t2_2*t2_3^2*t2_4 + 15*t2_2*t2_3*t2_4^2 + 2*t2_2*t2_4^3 + 6*t2_3^4 + 8*t2_3^3*t2_4 + 5*t2_3^2*t2_4^2 + t2_3*t2_4^3 by
                convert hleaf using 1 <;> ring
              positivity
      ·
        have h_t1_4_t1_1 := le_total t1_4 t1_1
        rcases h_t1_4_t1_1 with h_t1_4_t1_1 | h_t1_1_t1_4
        ·
          set t2_1 := t1_4
          set t2_2 := t1_1 - t1_4
          set t2_3 := t1_2 - t1_1
          set t2_4 := t1_3 - t1_2
          have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_4_nonneg
          have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
          have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
          have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
          have h_t1_1_eq : t1_1 = t2_1 + t2_2 := by
            dsimp [t2_1, t2_2]
            ring_nf
          have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 := by
            dsimp [t2_1, t2_2, t2_3]
            ring_nf
          have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 + t2_4 := by
            dsimp [t2_1, t2_2, t2_3, t2_4]
            ring_nf
          rw [h_t1_1_eq, h_t1_2_eq, h_t1_3_eq]
          suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 114*t2_1^3*t2_2 + 78*t2_1^3*t2_3 + 13*t2_1^3*t2_4 + 132*t2_1^2*t2_2^2 + 195*t2_1^2*t2_2*t2_3 + 25*t2_1^2*t2_2*t2_4 + 71*t2_1^2*t2_3^2 + 19*t2_1^2*t2_3*t2_4 + t2_1^2*t2_4^2 + 78*t2_1*t2_2^3 + 181*t2_1*t2_2^2*t2_3 + 22*t2_1*t2_2^2*t2_4 + 136*t2_1*t2_2*t2_3^2 + 38*t2_1*t2_2*t2_3*t2_4 + t2_1*t2_2*t2_4^2 + 33*t2_1*t2_3^3 + 16*t2_1*t2_3^2*t2_4 + t2_1*t2_3*t2_4^2 + 20*t2_2^4 + 62*t2_2^3*t2_3 + 9*t2_2^3*t2_4 + 70*t2_2^2*t2_3^2 + 23*t2_2^2*t2_3*t2_4 + t2_2^2*t2_4^2 + 34*t2_2*t2_3^3 + 19*t2_2*t2_3^2*t2_4 + 2*t2_2*t2_3*t2_4^2 + 6*t2_3^4 + 5*t2_3^3*t2_4 + t2_3^2*t2_4^2 by
            convert hleaf using 1 <;> ring
          positivity
        ·
          have h_t1_4_t1_2 := le_total t1_4 t1_2
          rcases h_t1_4_t1_2 with h_t1_4_t1_2 | h_t1_2_t1_4
          ·
            set t2_1 := t1_1
            set t2_2 := t1_4 - t1_1
            set t2_3 := t1_2 - t1_4
            set t2_4 := t1_3 - t1_2
            have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_1_nonneg
            have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
            have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
            have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
            have h_t1_4_eq : t1_4 = t2_1 + t2_2 := by
              dsimp [t2_1, t2_2]
              ring_nf
            have h_t1_2_eq : t1_2 = t2_1 + t2_2 + t2_3 := by
              dsimp [t2_1, t2_2, t2_3]
              ring_nf
            have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 + t2_4 := by
              dsimp [t2_1, t2_2, t2_3, t2_4]
              ring_nf
            rw [h_t1_4_eq, h_t1_2_eq, h_t1_3_eq]
            suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 124*t2_1^3*t2_2 + 78*t2_1^3*t2_3 + 13*t2_1^3*t2_4 + 140*t2_1^2*t2_2^2 + 181*t2_1^2*t2_2*t2_3 + 33*t2_1^2*t2_2*t2_4 + 71*t2_1^2*t2_3^2 + 19*t2_1^2*t2_3*t2_4 + t2_1^2*t2_4^2 + 68*t2_1*t2_2^3 + 136*t2_1*t2_2^2*t2_3 + 27*t2_1*t2_2^2*t2_4 + 105*t2_1*t2_2*t2_3^2 + 32*t2_1*t2_2*t2_3*t2_4 + 2*t2_1*t2_2*t2_4^2 + 33*t2_1*t2_3^3 + 16*t2_1*t2_3^2*t2_4 + t2_1*t2_3*t2_4^2 + 12*t2_2^4 + 33*t2_2^3*t2_3 + 7*t2_2^3*t2_4 + 38*t2_2^2*t2_3^2 + 13*t2_2^2*t2_3*t2_4 + t2_2^2*t2_4^2 + 23*t2_2*t2_3^3 + 12*t2_2*t2_3^2*t2_4 + t2_2*t2_3*t2_4^2 + 6*t2_3^4 + 5*t2_3^3*t2_4 + t2_3^2*t2_4^2 by
              convert hleaf using 1 <;> ring
            positivity
          ·
            have h_t1_4_t1_3 := le_total t1_4 t1_3
            rcases h_t1_4_t1_3 with h_t1_4_t1_3 | h_t1_3_t1_4
            ·
              set t2_1 := t1_1
              set t2_2 := t1_2 - t1_1
              set t2_3 := t1_4 - t1_2
              set t2_4 := t1_3 - t1_4
              have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_1_nonneg
              have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
              have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
              have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
              have h_t1_2_eq : t1_2 = t2_1 + t2_2 := by
                dsimp [t2_1, t2_2]
                ring_nf
              have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 := by
                dsimp [t2_1, t2_2, t2_3]
                ring_nf
              have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 + t2_4 := by
                dsimp [t2_1, t2_2, t2_3, t2_4]
                ring_nf
              rw [h_t1_2_eq, h_t1_4_eq, h_t1_3_eq]
              suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 124*t2_1^3*t2_2 + 59*t2_1^3*t2_3 + 13*t2_1^3*t2_4 + 140*t2_1^2*t2_2^2 + 132*t2_1^2*t2_2*t2_3 + 33*t2_1^2*t2_2*t2_4 + 45*t2_1^2*t2_3^2 + 16*t2_1^2*t2_3*t2_4 + t2_1^2*t2_4^2 + 68*t2_1*t2_2^3 + 95*t2_1*t2_2^2*t2_3 + 27*t2_1*t2_2^2*t2_4 + 61*t2_1*t2_2*t2_3^2 + 26*t2_1*t2_2*t2_3*t2_4 + 2*t2_1*t2_2*t2_4^2 + 16*t2_1*t2_3^3 + 13*t2_1*t2_3^2*t2_4 + t2_1*t2_3*t2_4^2 + 12*t2_2^4 + 22*t2_2^3*t2_3 + 7*t2_2^3*t2_4 + 20*t2_2^2*t2_3^2 + 10*t2_2^2*t2_3*t2_4 + t2_2^2*t2_4^2 + 10*t2_2*t2_3^3 + 9*t2_2*t2_3^2*t2_4 + t2_2*t2_3*t2_4^2 + 2*t2_3^4 + 3*t2_3^3*t2_4 + t2_3^2*t2_4^2 by
                convert hleaf using 1 <;> ring
              positivity
            ·
              set t2_1 := t1_1
              set t2_2 := t1_2 - t1_1
              set t2_3 := t1_3 - t1_2
              set t2_4 := t1_4 - t1_3
              have h_t2_1_nonneg : t2_1 ≥ 0 := h_t1_1_nonneg
              have h_t2_2_nonneg : t2_2 ≥ 0 := by linarith
              have h_t2_3_nonneg : t2_3 ≥ 0 := by linarith
              have h_t2_4_nonneg : t2_4 ≥ 0 := by linarith
              have h_t1_2_eq : t1_2 = t2_1 + t2_2 := by
                dsimp [t2_1, t2_2]
                ring_nf
              have h_t1_3_eq : t1_3 = t2_1 + t2_2 + t2_3 := by
                dsimp [t2_1, t2_2, t2_3]
                ring_nf
              have h_t1_4_eq : t1_4 = t2_1 + t2_2 + t2_3 + t2_4 := by
                dsimp [t2_1, t2_2, t2_3, t2_4]
                ring_nf
              rw [h_t1_2_eq, h_t1_3_eq, h_t1_4_eq]
              suffices hleaf : (0 : ℝ) ≤ 40*t2_1^4 + 124*t2_1^3*t2_2 + 59*t2_1^3*t2_3 + 46*t2_1^3*t2_4 + 140*t2_1^2*t2_2^2 + 132*t2_1^2*t2_2*t2_3 + 99*t2_1^2*t2_2*t2_4 + 45*t2_1^2*t2_3^2 + 74*t2_1^2*t2_3*t2_4 + 30*t2_1^2*t2_4^2 + 68*t2_1*t2_2^3 + 95*t2_1*t2_2^2*t2_3 + 68*t2_1*t2_2^2*t2_4 + 61*t2_1*t2_2*t2_3^2 + 96*t2_1*t2_2*t2_3*t2_4 + 37*t2_1*t2_2*t2_4^2 + 16*t2_1*t2_3^3 + 35*t2_1*t2_3^2*t2_4 + 23*t2_1*t2_3*t2_4^2 + 4*t2_1*t2_4^3 + 12*t2_2^4 + 22*t2_2^3*t2_3 + 15*t2_2^3*t2_4 + 20*t2_2^2*t2_3^2 + 30*t2_2^2*t2_3*t2_4 + 11*t2_2^2*t2_4^2 + 10*t2_2*t2_3^3 + 21*t2_2*t2_3^2*t2_4 + 13*t2_2*t2_3*t2_4^2 + 2*t2_2*t2_4^3 + 2*t2_3^4 + 5*t2_3^3*t2_4 + 4*t2_3^2*t2_4^2 + t2_3*t2_4^3 by
                convert hleaf using 1 <;> ring
              positivity

private theorem private_hDS_class_6 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^3*b + a^3*c + a^2*b^2 - a^2*b*c - a^2*b*d - 2*a^2*c^2 + a^2*d^2 - a*b^2*c - a*b*d^2 + a*c^3 - a*c^2*d - a*c*d^2 + a*d^3 + b^3*c + b^3*d + b^2*c^2 - b^2*c*d - 2*b^2*d^2 - b*c^2*d + b*d^3 + c^3*d + c^2*d^2 := by
  intro a b c d h_a_nonneg_base h_b_nonneg_base h_c_nonneg_base h_d_nonneg_base hsort
  have h_a_b : a ≤ b := hsort.1
  have h_b_c : b ≤ c := hsort.2.1
  have h_c_d : c ≤ d := hsort.2.2
  set t1_1 := a
  set t1_2 := b - a
  set t1_3 := c - b
  set t1_4 := d - c
  have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
  have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
  have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
  have h_t1_4_nonneg : t1_4 ≥ 0 := by linarith
  have h_b_eq : b = t1_1 + t1_2 := by
    dsimp [t1_1, t1_2]
    ring_nf
  have h_c_eq : c = t1_1 + t1_2 + t1_3 := by
    dsimp [t1_1, t1_2, t1_3]
    ring_nf
  have h_d_eq : d = t1_1 + t1_2 + t1_3 + t1_4 := by
    dsimp [t1_1, t1_2, t1_3, t1_4]
    ring_nf
  rw [h_b_eq, h_c_eq, h_d_eq]
  suffices hleaf : (0 : ℝ) ≤ 4*t1_1^2*t1_2^2 + 8*t1_1^2*t1_2*t1_3 + 8*t1_1^2*t1_3^2 + 8*t1_1^2*t1_3*t1_4 + 4*t1_1^2*t1_4^2 + 6*t1_1*t1_2^3 + 15*t1_1*t1_2^2*t1_3 + t1_1*t1_2^2*t1_4 + 19*t1_1*t1_2*t1_3^2 + 14*t1_1*t1_2*t1_3*t1_4 + 5*t1_1*t1_2*t1_4^2 + 8*t1_1*t1_3^3 + 11*t1_1*t1_3^2*t1_4 + 7*t1_1*t1_3*t1_4^2 + 2*t1_1*t1_4^3 + 2*t1_2^4 + 6*t1_2^3*t1_3 + t1_2^3*t1_4 + 10*t1_2^2*t1_3^2 + 8*t1_2^2*t1_3*t1_4 + 2*t1_2^2*t1_4^2 + 8*t1_2*t1_3^3 + 11*t1_2*t1_3^2*t1_4 + 5*t1_2*t1_3*t1_4^2 + t1_2*t1_4^3 + 2*t1_3^4 + 3*t1_3^3*t1_4 + t1_3^2*t1_4^2 by
    convert hleaf using 1 <;> ring
  positivity

theorem real_p2' (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) ≥ 2 := by
  rw [ge_iff_le]
  rw [← sub_nonneg]
  have hden1_pos : 0 < b + c := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd]
  have hden1_ne : b + c ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < c + d := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd]
  have hden2_ne : c + d ≠ 0 := ne_of_gt hden2_pos
  have hden3_pos : 0 < a + d := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd]
  have hden3_ne : a + d ≠ 0 := ne_of_gt hden3_pos
  have hden4_pos : 0 < a + b := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd]
  have hden4_ne : a + b ≠ 0 := ne_of_gt hden4_pos
  field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm, hd.ne.symm, hden1_pos, hden2_pos, hden3_pos, hden4_pos]
  ring_nf
  clear hden1_pos hden2_pos hden3_pos hden4_pos hden1_ne hden2_ne hden3_ne hden4_ne
  have hDS_class_1 := private_hDS_class_1
  have hDS_class_2 := private_hDS_class_2
  have hDS_class_3 := private_hDS_class_3
  have hDS_class_4 := private_hDS_class_4
  have hDS_class_5 := private_hDS_class_5
  have hDS_class_6 := private_hDS_class_6
  have h_b_a := le_total b a
  rcases h_b_a with h_b_a | h_a_b
  ·
    have h_c_b := le_total c b
    rcases h_c_b with h_c_b | h_b_c
    ·
      have h_d_c := le_total d c
      rcases h_d_c with h_d_c | h_c_d
      ·
        have hs : d ≤ c ∧ c ≤ b ∧ b ≤ a := by
          constructor
          · linarith
          ·
            constructor
            · linarith
            ·
              linarith
        have hcert := hDS_class_6 d c b a (by positivity) (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring
      ·
        have h_d_b := le_total d b
        rcases h_d_b with h_d_b | h_b_d
        ·
          have hs : c ≤ d ∧ d ≤ b ∧ b ≤ a := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_2 c d b a (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_a := le_total d a
          rcases h_d_a with h_d_a | h_a_d
          ·
            have hs : c ≤ b ∧ b ≤ d ∧ d ≤ a := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_4 c b d a (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have hs : c ≤ b ∧ b ≤ a ∧ a ≤ d := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_6 c b a d (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
    ·
      have h_c_a := le_total c a
      rcases h_c_a with h_c_a | h_a_c
      ·
        have h_d_b := le_total d b
        rcases h_d_b with h_d_b | h_b_d
        ·
          have hs : d ≤ b ∧ b ≤ c ∧ c ≤ a := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_5 d b c a (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_c := le_total d c
          rcases h_d_c with h_d_c | h_c_d
          ·
            have hs : b ≤ d ∧ d ≤ c ∧ c ≤ a := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_3 b d c a (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have h_d_a := le_total d a
            rcases h_d_a with h_d_a | h_a_d
            ·
              have hs : b ≤ c ∧ c ≤ d ∧ d ≤ a := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_1 b c d a (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
            ·
              have hs : b ≤ c ∧ c ≤ a ∧ a ≤ d := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_2 b c a d (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
      ·
        have h_d_b := le_total d b
        rcases h_d_b with h_d_b | h_b_d
        ·
          have hs : d ≤ b ∧ b ≤ a ∧ a ≤ c := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_3 d b a c (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_a := le_total d a
          rcases h_d_a with h_d_a | h_a_d
          ·
            have hs : b ≤ d ∧ d ≤ a ∧ a ≤ c := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_5 b d a c (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have h_d_c := le_total d c
            rcases h_d_c with h_d_c | h_c_d
            ·
              have hs : b ≤ a ∧ a ≤ d ∧ d ≤ c := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_6 b a d c (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
            ·
              have hs : b ≤ a ∧ a ≤ c ∧ c ≤ d := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_4 b a c d (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
  ·
    have h_c_a := le_total c a
    rcases h_c_a with h_c_a | h_a_c
    ·
      have h_d_c := le_total d c
      rcases h_d_c with h_d_c | h_c_d
      ·
        have hs : d ≤ c ∧ c ≤ a ∧ a ≤ b := by
          constructor
          · linarith
          ·
            constructor
            · linarith
            ·
              linarith
        have hcert := hDS_class_4 d c a b (by positivity) (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring
      ·
        have h_d_a := le_total d a
        rcases h_d_a with h_d_a | h_a_d
        ·
          have hs : c ≤ d ∧ d ≤ a ∧ a ≤ b := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_1 c d a b (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_b := le_total d b
          rcases h_d_b with h_d_b | h_b_d
          ·
            have hs : c ≤ a ∧ a ≤ d ∧ d ≤ b := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_3 c a d b (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have hs : c ≤ a ∧ a ≤ b ∧ b ≤ d := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_5 c a b d (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
    ·
      have h_c_b := le_total c b
      rcases h_c_b with h_c_b | h_b_c
      ·
        have h_d_a := le_total d a
        rcases h_d_a with h_d_a | h_a_d
        ·
          have hs : d ≤ a ∧ a ≤ c ∧ c ≤ b := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_2 d a c b (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_c := le_total d c
          rcases h_d_c with h_d_c | h_c_d
          ·
            have hs : a ≤ d ∧ d ≤ c ∧ c ≤ b := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_6 a d c b (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have h_d_b := le_total d b
            rcases h_d_b with h_d_b | h_b_d
            ·
              have hs : a ≤ c ∧ c ≤ d ∧ d ≤ b := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_5 a c d b (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
            ·
              have hs : a ≤ c ∧ c ≤ b ∧ b ≤ d := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_3 a c b d (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
      ·
        have h_d_a := le_total d a
        rcases h_d_a with h_d_a | h_a_d
        ·
          have hs : d ≤ a ∧ a ≤ b ∧ b ≤ c := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_1 d a b c (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_b := le_total d b
          rcases h_d_b with h_d_b | h_b_d
          ·
            have hs : a ≤ d ∧ d ≤ b ∧ b ≤ c := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_4 a d b c (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have h_d_c := le_total d c
            rcases h_d_c with h_d_c | h_c_d
            ·
              have hs : a ≤ b ∧ b ≤ d ∧ d ≤ c := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_2 a b d c (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
            ·
              have hs : a ≤ b ∧ b ≤ c ∧ c ≤ d := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_1 a b c d (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring



theorem real_p2 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : a / (b + c) + b / (c + d) + c / (d + a) + d / (a + b) ≥ 2 := by
  exact @real_p2' a b c d ha hb hc hd
