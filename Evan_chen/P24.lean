import Mathlib
open Real

theorem P24 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) : 1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2) ≤ 1 / (6 * sqrt (a * b) + c) + 1 / (6 * sqrt (b * c) + a) + 1 / (6 * sqrt (c * a) + b) := by
  have ha1 : a < 1 := by nlinarith [hb, hc, h]
  have hb1 : b < 1 := by nlinarith [ha, hc, h]
  have hc1 : c < 1 := by nlinarith [ha, hb, h]
  -- Tangent lower bound: 1 / (3 - 2 * t) ≥ 1 / (t + 2) + (27 / 49) * (t - 1 / 3)
  have hlin (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
      1 / (t + 2) + (27 / 49) * (t - 1 / 3) ≤ 1 / (3 - 2 * t) := by
    have hd1 : t + 2 ≠ 0 := by positivity
    have hd2 : 3 - 2 * t ≠ 0 := by nlinarith [ht1]
    have hd1p : 0 < t + 2 := by positivity
    have hd2p : 0 < 3 - 2 * t := by nlinarith [ht1]
    have hN : 0 ≤ (9 / 49) * (t - 1 / 3) ^ 2 * (6 * t + 5) := by positivity
    have hid :
        1 / (3 - 2 * t) - 1 / (t + 2) - (27 / 49) * (t - 1 / 3) =
          ((9 / 49) * (t - 1 / 3) ^ 2 * (6 * t + 5)) / ((3 - 2 * t) * (t + 2)) := by
      field_simp [hd1, hd2]
      ring
    have hq : 0 ≤ 1 / (3 - 2 * t) - 1 / (t + 2) - (27 / 49) * (t - 1 / 3) := by
      rw [hid]
      exact div_nonneg hN (le_of_lt (mul_pos hd2p hd1p))
    linarith
  have hlin_a : 1 / (a + 2) + (27 / 49) * (a - 1 / 3) ≤ 1 / (3 - 2 * a) := hlin a ha ha1
  have hlin_b : 1 / (b + 2) + (27 / 49) * (b - 1 / 3) ≤ 1 / (3 - 2 * b) := hlin b hb hb1
  have hlin_c : 1 / (c + 2) + (27 / 49) * (c - 1 / 3) ≤ 1 / (3 - 2 * c) := hlin c hc hc1
  have hmid : 1 / (a + 2) + 1 / (b + 2) + 1 / (c + 2) ≤
      1 / (3 - 2 * a) + 1 / (3 - 2 * b) + 1 / (3 - 2 * c) := by
    nlinarith [hlin_a, hlin_b, hlin_c, h]
  -- AM-GM bound for each square root
  have hamgm (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : sqrt (x * y) ≤ (x + y) / 2 := by
    have hxy0 : 0 ≤ x * y := by positivity
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_nonneg (x - y)]
  have hsab : sqrt (a * b) ≤ (a + b) / 2 := hamgm a b ha hb
  have hsbc : sqrt (b * c) ≤ (b + c) / 2 := hamgm b c hb hc
  have hsca : sqrt (c * a) ≤ (c + a) / 2 := hamgm c a hc ha
  have hbda : 6 * sqrt (a * b) + c ≤ 3 - 2 * c := by nlinarith [hsab, h]
  have hbdb : 6 * sqrt (b * c) + a ≤ 3 - 2 * a := by nlinarith [hsbc, h]
  have hbdc : 6 * sqrt (c * a) + b ≤ 3 - 2 * b := by nlinarith [hsca, h]
  have hpa : 0 < 6 * sqrt (a * b) + c := by
    nlinarith [Real.sqrt_nonneg (a * b), hc]
  have hpb : 0 < 6 * sqrt (b * c) + a := by
    nlinarith [Real.sqrt_nonneg (b * c), ha]
  have hpc : 0 < 6 * sqrt (c * a) + b := by
    nlinarith [Real.sqrt_nonneg (c * a), hb]
  have hta : 1 / (3 - 2 * c) ≤ 1 / (6 * sqrt (a * b) + c) :=
    one_div_le_one_div_of_le hpa hbda
  have htb : 1 / (3 - 2 * a) ≤ 1 / (6 * sqrt (b * c) + a) :=
    one_div_le_one_div_of_le hpb hbdb
  have htc : 1 / (3 - 2 * b) ≤ 1 / (6 * sqrt (c * a) + b) :=
    one_div_le_one_div_of_le hpc hbdc
  have hright : 1 / (3 - 2 * a) + 1 / (3 - 2 * b) + 1 / (3 - 2 * c) ≤
      1 / (6 * sqrt (a * b) + c) + 1 / (6 * sqrt (b * c) + a) +
        1 / (6 * sqrt (c * a) + b) := by
    nlinarith [hta, htb, htc]
  nlinarith [hmid, hright]
