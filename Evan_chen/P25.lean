import Mathlib

theorem P25 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h : a + b + c = 1) :
    1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2) ≤
      1 / (3 - 2 * c) + 1 / (3 - 2 * a) + 1 / (3 - 2 * b) := by
  have key (x : ℝ) (hx0 : x > 0) (hx1 : x < 1) :
      49 * (1 / (3 - 2 * x) - 1 / (x + 2)) - 27 * (x - 1 / 3) ≥ 0 := by
    have h3 : 0 < 3 - 2 * x := by nlinarith
    have hx2 : 0 < x + 2 := by nlinarith
    have hD : 0 < (3 - 2 * x) * (x + 2) := mul_pos h3 hx2
    have h6 : 0 < 6 * x + 5 := by nlinarith
    have hP : 0 ≤ (3 * x - 1) ^ 2 * (6 * x + 5) :=
      mul_nonneg (sq_nonneg (3 * x - 1)) (le_of_lt h6)
    let T : ℝ := 49 * (1 / (3 - 2 * x) - 1 / (x + 2)) - 27 * (x - 1 / 3)
    let D : ℝ := (3 - 2 * x) * (x + 2)
    let P : ℝ := (3 * x - 1) ^ 2 * (6 * x + 5)
    have hTcalc : T * D = P := by
      subst T; subst D; subst P
      field_simp [h3.ne', hx2.ne']
      ring
    have hT : 0 ≤ T := by
      exact (mul_nonneg_iff_of_pos_right (by simpa [D] using hD)).mp (by
        rw [hTcalc]
        simpa [P] using hP)
    simpa [T] using hT
  have ha1 : a < 1 := by nlinarith
  have hb1 : b < 1 := by nlinarith
  have hc1 : c < 1 := by nlinarith
  have ka := key a ha ha1
  have kb := key b hb hb1
  have kc := key c hc hc1
  let S : ℝ := (1 / (3 - 2 * c) - 1 / (c + 2)) +
      (1 / (3 - 2 * a) - 1 / (a + 2)) + (1 / (3 - 2 * b) - 1 / (b + 2))
  have hS : 0 ≤ 49 * S := by
    have : 0 ≤ 49 * S - 27 * ((a - 1 / 3) + (b - 1 / 3) + (c - 1 / 3)) := by
      nlinarith [ka, kb, kc]
    nlinarith [h]
  have hS0 : 0 ≤ S := by nlinarith
  nlinarith
