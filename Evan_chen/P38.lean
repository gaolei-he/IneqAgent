import Mathlib

open Real

theorem P38 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 3) : sqrt 3 ≤ sqrt (a ^ 2 + a * b + b ^ 2) + sqrt (b ^ 2 + b * c + c ^ 2) + sqrt (c ^ 2 + c * a + a ^ 2) := by
  have term_bound : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y →
      (sqrt 3 / 2) * (x + y) ≤ sqrt (x ^ 2 + x * y + y ^ 2) := by
    intro x y hx hy
    apply Real.le_sqrt_of_sq_le
    have hs3sq : (sqrt 3) ^ 2 = 3 := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hdiff : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
    nlinarith [hs3sq, hdiff]
  have h1 := term_bound ha.le hb.le
  have h2 := term_bound hb.le hc.le
  have h3 := term_bound hc.le ha.le
  calc
    sqrt 3 ≤ 3 * sqrt 3 := by
      have hs : 0 ≤ sqrt 3 := sqrt_nonneg 3
      nlinarith
    _ = (sqrt 3 / 2) * (a + b) + (sqrt 3 / 2) * (b + c) + (sqrt 3 / 2) * (c + a) := by
      rw [← h]
      ring
    _ ≤ sqrt (a ^ 2 + a * b + b ^ 2) + sqrt (b ^ 2 + b * c + c ^ 2) + sqrt (c ^ 2 + c * a + a ^ 2) := by
      exact add_le_add (add_le_add h1 h2) h3
