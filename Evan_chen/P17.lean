import Mathlib
open Real

private lemma sqrt_add_le_two_sqrt {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huvw : u + v = 2 * w) : sqrt u + sqrt v ≤ 2 * sqrt w := by
  have hw : 0 ≤ w := by nlinarith
  have hpair : sqrt u + sqrt v ≤ sqrt (2 * (u + v)) := by
    apply le_sqrt_of_sq_le
    have hu2 : sqrt u ^ 2 = u := sq_sqrt hu
    have hv2 : sqrt v ^ 2 = v := sq_sqrt hv
    nlinarith [sq_nonneg (sqrt u - sqrt v), hu2, hv2]
  calc
    sqrt u + sqrt v ≤ sqrt (2 * (u + v)) := hpair
    _ = sqrt (2 * (2 * w)) := by rw [huvw]
    _ = 2 * sqrt w := by
      have hmul : 2 * (2 * w) = 4 * w := by ring
      rw [hmul, Real.sqrt_mul' (4 : ℝ) hw]
      norm_num

theorem P17 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h1 : a + b > c) (h2 : a + c > b) (hc : b + c > a): sqrt (a + b - c) + sqrt (b + c - a) + sqrt (c + a - b) ≤ sqrt (a) + sqrt (b) + sqrt (c) := by
  have hc_pair : sqrt (b + c - a) + sqrt (c + a - b) ≤ 2 * sqrt c := by
    apply sqrt_add_le_two_sqrt
    · linarith
    · linarith
    · ring
  have hb_pair : sqrt (a + b - c) + sqrt (b + c - a) ≤ 2 * sqrt b := by
    apply sqrt_add_le_two_sqrt
    · linarith
    · linarith
    · ring
  have ha_pair : sqrt (c + a - b) + sqrt (a + b - c) ≤ 2 * sqrt a := by
    apply sqrt_add_le_two_sqrt
    · linarith
    · linarith
    · ring
  nlinarith
