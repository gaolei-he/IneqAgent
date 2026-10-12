import Mathlib

theorem P12 (a b c : ℝ) : |a*b*(a^2 - b^2) + b*c*(b^2 - c^2) + c*a*(c^2 - a^2)| ≤ 9/(16*2^(1/2)) * (a^2 + b^2 + c^2)^2 := by
  have hfactor :
      a*b*(a^2 - b^2) + b*c*(b^2 - c^2) + c*a*(c^2 - a^2)
        = (a - b) * (a - c) * (b - c) * (a + b + c) := by
    ring
  have hpow_half : (2 : ℝ) ^ (1 / 2) = 1 := by
    norm_num
  have hS_nonneg : 0 ≤ a^2 + b^2 + c^2 := by
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hR_nonneg : 0 ≤ 9 / (16 * 2 ^ (1 / 2)) * (a^2 + b^2 + c^2)^2 := by
    rw [hpow_half]
    nlinarith [sq_nonneg (a^2 + b^2 + c^2)]
  have h_abs_from_square :
      ((a - b) * (a - c) * (b - c) * (a + b + c)) ^ 2
        ≤ (9 / (16 * 2 ^ (1 / 2)) * (a^2 + b^2 + c^2)^2) ^ 2 →
      |a*b*(a^2 - b^2) + b*c*(b^2 - c^2) + c*a*(c^2 - a^2)|
        ≤ 9 / (16 * 2 ^ (1 / 2)) * (a^2 + b^2 + c^2)^2 := by
    intro hsquare
    rw [hfactor]
    exact abs_le_of_sq_le_sq hsquare hR_nonneg
  have hdiff_sq_le (u v : ℝ) : (u^2 - v^2)^2 ≤ (u^2 + v^2)^2 := by
    nlinarith [sq_nonneg u, sq_nonneg v]
  have hcore (u v x : ℝ) :
      u^2 * x^2 * (u^2 + v^2)^2 / 16
        ≤ (9 / 16 * (((3*u^2 + v^2 + 2*x^2) / 6)^2)) ^ 2 := by
    let A : ℝ := u^2
    let B : ℝ := v^2
    let C : ℝ := x^2
    let r : ℝ := A + B
    let s : ℝ := A + C
    let T : ℝ := 3*A + B + 2*C
    have hA : 0 ≤ A := by dsimp [A]; exact sq_nonneg u
    have hB : 0 ≤ B := by dsimp [B]; exact sq_nonneg v
    have hC : 0 ≤ C := by dsimp [C]; exact sq_nonneg x
    have hr : 0 ≤ r := by dsimp [r]; nlinarith
    have hs : 0 ≤ s := by dsimp [s]; nlinarith
    have hACdiff : 0 ≤ s^2 - 4*A*C := by
      dsimp [s]
      nlinarith [sq_nonneg (A - C)]
    have hr2 : 0 ≤ 64 * r^2 := by nlinarith [sq_nonneg r]
    have hACmul : 0 ≤ (64 * r^2) * (s^2 - 4*A*C) := mul_nonneg hr2 hACdiff
    have hACbound : 256*A*C*r^2 ≤ 64*r^2*s^2 := by
      nlinarith
    have hTdiff : 0 ≤ T^2 - 8*r*s := by
      dsimp [T, r, s]
      nlinarith [sq_nonneg ((A + B) - 2*(A + C))]
    have hTsum : 0 ≤ T^2 + 8*r*s := by nlinarith [sq_nonneg T, mul_nonneg hr hs]
    have hTmul : 0 ≤ (T^2 - 8*r*s) * (T^2 + 8*r*s) := mul_nonneg hTdiff hTsum
    have hTbound : 64*r^2*s^2 ≤ T^4 := by
      nlinarith
    have hmain : 256*A*C*r^2 ≤ T^4 := by nlinarith
    dsimp [A, B, C, r, s, T] at hmain ⊢
    nlinarith
  have hcoord_norm :
      ((3*(a - b)^2 + (a + b - 2*c)^2 + 2*(a + b + c)^2) / 6)
        = a^2 + b^2 + c^2 := by
    ring
  have hprod_sq_le :
      ((a - b) * (a - c) * (b - c) * (a + b + c)) ^ 2
        ≤ (a - b)^2 * (a + b + c)^2 * ((a - b)^2 + (a + b - 2*c)^2)^2 / 16 := by
    have hdiff := hdiff_sq_le (a - b) (a + b - 2*c)
    have hprod_sq_eq :
        ((a - b) * (a - c) * (b - c) * (a + b + c)) ^ 2
          = (a - b)^2 * (a + b + c)^2 * ((a - b)^2 - (a + b - 2*c)^2)^2 / 16 := by
      ring
    rw [hprod_sq_eq]
    have hscale_nonneg : 0 ≤ (a - b)^2 * (a + b + c)^2 / 16 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b + c),
        mul_nonneg (sq_nonneg (a - b)) (sq_nonneg (a + b + c))]
    have hscaled := mul_le_mul_of_nonneg_left hdiff hscale_nonneg
    nlinarith
  have hcore_inst :
      (a - b)^2 * (a + b + c)^2 * ((a - b)^2 + (a + b - 2*c)^2)^2 / 16
        ≤ (9 / 16 * (a^2 + b^2 + c^2)^2) ^ 2 := by
    have h := hcore (a - b) (a + b - 2*c) (a + b + c)
    rw [hcoord_norm] at h
    exact h
  have hsquare :
      ((a - b) * (a - c) * (b - c) * (a + b + c)) ^ 2
        ≤ (9 / (16 * 2 ^ (1 / 2)) * (a^2 + b^2 + c^2)^2) ^ 2 := by
    rw [hpow_half]
    norm_num
    exact le_trans hprod_sq_le hcore_inst
  exact h_abs_from_square hsquare
