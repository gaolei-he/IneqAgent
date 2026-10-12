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

namespace Lean92.MO_INT_20_P2

theorem P2 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : 2 / 3 ≤ a / (b + 2 * c + 3 * d) + b / (c + 2 * d + 3 * a) + c / (d + 2 * a + 3 * b) + d / (a + 2 * b + 3 * c) := by
  rw [← sub_nonneg]
  have hden1_pos : 0 < b + 2*c + 3*d := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd]
  have hden1_ne : b + 2*c + 3*d ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < 3*a + c + 2*d := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd]
  have hden2_ne : 3*a + c + 2*d ≠ 0 := ne_of_gt hden2_pos
  have hden3_pos : 0 < 2*a + 3*b + d := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd]
  have hden3_ne : 2*a + 3*b + d ≠ 0 := ne_of_gt hden3_pos
  have hden4_pos : 0 < a + 2*b + 3*c := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd]
  have hden4_ne : a + 2*b + 3*c ≠ 0 := ne_of_gt hden4_pos
  field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm, hd.ne.symm, hden1_pos, hden2_pos, hden3_pos, hden4_pos]
  ring_nf
  clear hden1_pos hden2_pos hden3_pos hden4_pos hden1_ne hden2_ne hden3_ne hden4_ne
  have hDS_class_1 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ 18*a^4 + 51*a^3*b + 36*a^3*c - 15*a^3*d + 18*a^2*b^2 - a^2*b*c - 44*a^2*b*d - 44*a^2*c^2 - 19*a^2*c*d + 18*a^2*d^2 - 15*a*b^3 - 44*a*b^2*c - 19*a*b^2*d - 19*a*b*c^2 - 88*a*b*c*d - a*b*d^2 + 36*a*c^3 - a*c^2*d - 44*a*c*d^2 + 51*a*d^3 + 18*b^4 + 51*b^3*c + 36*b^3*d + 18*b^2*c^2 - b^2*c*d - 44*b^2*d^2 - 15*b*c^3 - 44*b*c^2*d - 19*b*c*d^2 + 36*b*d^3 + 18*c^4 + 51*c^3*d + 18*c^2*d^2 - 15*c*d^3 + 18*d^4 := by
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
    ring_nf
    positivity
  have hDS_class_2 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ 18*a^4 + 51*a^3*b - 15*a^3*c + 36*a^3*d + 18*a^2*b^2 - 44*a^2*b*c - a^2*b*d + 18*a^2*c^2 - 19*a^2*c*d - 44*a^2*d^2 - 15*a*b^3 - 19*a*b^2*c - 44*a*b^2*d - a*b*c^2 - 88*a*b*c*d - 19*a*b*d^2 + 51*a*c^3 - 44*a*c^2*d - a*c*d^2 + 36*a*d^3 + 18*b^4 + 36*b^3*c + 51*b^3*d - 44*b^2*c^2 - b^2*c*d + 18*b^2*d^2 + 36*b*c^3 - 19*b*c^2*d - 44*b*c*d^2 - 15*b*d^3 + 18*c^4 - 15*c^3*d + 18*c^2*d^2 + 51*c*d^3 + 18*d^4 := by
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
    ring_nf
    positivity
  have hDS_class_3 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ 18*a^4 + 36*a^3*b + 51*a^3*c - 15*a^3*d - 44*a^2*b^2 - a^2*b*c - 19*a^2*b*d + 18*a^2*c^2 - 44*a^2*c*d + 18*a^2*d^2 + 36*a*b^3 - 19*a*b^2*c - a*b^2*d - 44*a*b*c^2 - 88*a*b*c*d - 44*a*b*d^2 - 15*a*c^3 - 19*a*c^2*d - a*c*d^2 + 51*a*d^3 + 18*b^4 - 15*b^3*c + 51*b^3*d + 18*b^2*c^2 - 44*b^2*c*d + 18*b^2*d^2 + 51*b*c^3 - b*c^2*d - 19*b*c*d^2 - 15*b*d^3 + 18*c^4 + 36*c^3*d - 44*c^2*d^2 + 36*c*d^3 + 18*d^4 := by
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
    ring_nf
    positivity
  have hDS_class_4 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ 18*a^4 - 15*a^3*b + 51*a^3*c + 36*a^3*d + 18*a^2*b^2 - 44*a^2*b*c - 19*a^2*b*d + 18*a^2*c^2 - a^2*c*d - 44*a^2*d^2 + 51*a*b^3 - a*b^2*c - 44*a*b^2*d - 19*a*b*c^2 - 88*a*b*c*d - a*b*d^2 - 15*a*c^3 - 44*a*c^2*d - 19*a*c*d^2 + 36*a*d^3 + 18*b^4 + 36*b^3*c - 15*b^3*d - 44*b^2*c^2 - 19*b^2*c*d + 18*b^2*d^2 + 36*b*c^3 - b*c^2*d - 44*b*c*d^2 + 51*b*d^3 + 18*c^4 + 51*c^3*d + 18*c^2*d^2 - 15*c*d^3 + 18*d^4 := by
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
    ring_nf
    positivity
  have hDS_class_5 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ 18*a^4 + 36*a^3*b - 15*a^3*c + 51*a^3*d - 44*a^2*b^2 - 19*a^2*b*c - a^2*b*d + 18*a^2*c^2 - 44*a^2*c*d + 18*a^2*d^2 + 36*a*b^3 - a*b^2*c - 19*a*b^2*d - 44*a*b*c^2 - 88*a*b*c*d - 44*a*b*d^2 + 51*a*c^3 - a*c^2*d - 19*a*c*d^2 - 15*a*d^3 + 18*b^4 + 51*b^3*c - 15*b^3*d + 18*b^2*c^2 - 44*b^2*c*d + 18*b^2*d^2 - 15*b*c^3 - 19*b*c^2*d - b*c*d^2 + 51*b*d^3 + 18*c^4 + 36*c^3*d - 44*c^2*d^2 + 36*c*d^3 + 18*d^4 := by
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
    ring_nf
    positivity
  have hDS_class_6 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ 18*a^4 - 15*a^3*b + 36*a^3*c + 51*a^3*d + 18*a^2*b^2 - 19*a^2*b*c - 44*a^2*b*d - 44*a^2*c^2 - a^2*c*d + 18*a^2*d^2 + 51*a*b^3 - 44*a*b^2*c - a*b^2*d - a*b*c^2 - 88*a*b*c*d - 19*a*b*d^2 + 36*a*c^3 - 19*a*c^2*d - 44*a*c*d^2 - 15*a*d^3 + 18*b^4 - 15*b^3*c + 36*b^3*d + 18*b^2*c^2 - 19*b^2*c*d - 44*b^2*d^2 + 51*b*c^3 - 44*b*c^2*d - b*c*d^2 + 36*b*d^3 + 18*c^4 - 15*c^3*d + 18*c^2*d^2 + 51*c*d^3 + 18*d^4 := by
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
    ring_nf
    positivity
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
        convert hcert using 1 <;> ring_nf
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
          convert hcert using 1 <;> ring_nf
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
            convert hcert using 1 <;> ring_nf
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
            convert hcert using 1 <;> ring_nf
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
          convert hcert using 1 <;> ring_nf
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
            convert hcert using 1 <;> ring_nf
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
              convert hcert using 1 <;> ring_nf
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
              convert hcert using 1 <;> ring_nf
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
          convert hcert using 1 <;> ring_nf
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
            convert hcert using 1 <;> ring_nf
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
              convert hcert using 1 <;> ring_nf
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
              convert hcert using 1 <;> ring_nf
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
        convert hcert using 1 <;> ring_nf
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
          convert hcert using 1 <;> ring_nf
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
            convert hcert using 1 <;> ring_nf
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
            convert hcert using 1 <;> ring_nf
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
          convert hcert using 1 <;> ring_nf
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
            convert hcert using 1 <;> ring_nf
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
              convert hcert using 1 <;> ring_nf
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
              convert hcert using 1 <;> ring_nf
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
          convert hcert using 1 <;> ring_nf
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
            convert hcert using 1 <;> ring_nf
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
              convert hcert using 1 <;> ring_nf
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
              convert hcert using 1 <;> ring_nf

end Lean92.MO_INT_20_P2


theorem P2 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : 2 / 3 ≤ a / (b + 2 * c + 3 * d) + b / (c + 2 * d + 3 * a) + c / (d + 2 * a + 3 * b) + d / (a + 2 * b + 3 * c) := by
  exact @Lean92.MO_INT_20_P2.P2 a b c d ha hb hc hd

#print axioms P2
