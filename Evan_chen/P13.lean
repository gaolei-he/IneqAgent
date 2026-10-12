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

namespace Lean92.Evan_chen_P13

theorem P13 {a b c d : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (h : a * b * c * d = 1) : a + b + c + d ≤ a ^ 4 * b + b ^ 4 * c + c ^ 4 * d + d ^ 4 * a := by
  rw [← sub_nonneg]
  field_simp
  ring_nf
  have hQ : a*b*c*d = 1 := by nlinarith [h]
  have hQunit : a*b*c*d = 1 := by nlinarith [hQ]
  suffices hH :
      0 ≤ a^4*b + a*d^4 + (-a)*(a*b*c*d) + b^4*c + (-b)*(a*b*c*d) + c^4*d + (-c)*(a*b*c*d) + (-d)*(a*b*c*d) by
    convert hH using 1
    try rw [hQunit]
    try rw [hQ]
    ring_nf
  ring_nf
  clear h hQ hQunit
  have hDS_class_1 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^4*b - a^2*b*c*d - a*b^2*c*d - a*b*c^2*d - a*b*c*d^2 + a*d^4 + b^4*c + c^4*d := by
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
  have hDS_class_2 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^4*b - a^2*b*c*d - a*b^2*c*d - a*b*c^2*d - a*b*c*d^2 + a*c^4 + b^4*d + c*d^4 := by
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
  have hDS_class_3 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^4*c - a^2*b*c*d - a*b^2*c*d - a*b*c^2*d - a*b*c*d^2 + a*d^4 + b^4*d + b*c^4 := by
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
  have hDS_class_4 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^4*c - a^2*b*c*d + a*b^4 - a*b^2*c*d - a*b*c^2*d - a*b*c*d^2 + b*d^4 + c^4*d := by
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
  have hDS_class_5 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^4*d - a^2*b*c*d - a*b^2*c*d - a*b*c^2*d - a*b*c*d^2 + a*c^4 + b^4*c + b*d^4 := by
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
  have hDS_class_6 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^4*d - a^2*b*c*d + a*b^4 - a*b^2*c*d - a*b*c^2*d - a*b*c*d^2 + b*c^4 + c*d^4 := by
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

end Lean92.Evan_chen_P13


theorem P13 {a b c d : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (h : a * b * c * d = 1) : a + b + c + d ≤ a ^ 4 * b + b ^ 4 * c + c ^ 4 * d + d ^ 4 * a := by
  exact @Lean92.Evan_chen_P13.P13 a b c d ha hb hc hd h

#print axioms P13
