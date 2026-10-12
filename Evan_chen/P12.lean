import Mathlib

private lemma term_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b + a * c + b * c ≤ 2) :
    1 + ((b + c) * (c + a)) / (a + b) ^ 2 ≤
      2 * (a * b + 1) / (a + b) ^ 2 := by
  have hposab : 0 < a + b := add_pos ha hb
  field_simp [ne_of_gt hposab]
  nlinarith [h]

private lemma cyclic_sum_ge_three {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    3 ≤ y * z / x ^ 2 + z * x / y ^ 2 + x * y / z ^ 2 := by
  have hc : 3 * (y * z) * (z * x) * (x * y) ≤ (y * z) ^ 3 + (z * x) ^ 3 + (x * y) ^ 3 := by
    have hsq :
        0 ≤ (y * z) ^ 2 + (z * x) ^ 2 + (x * y) ^ 2 - (y * z) * (z * x) -
          (y * z) * (x * y) - (z * x) * (x * y) := by
      nlinarith [sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x * y - y * z)]
    have hsum : 0 ≤ (y * z) + (z * x) + (x * y) := by nlinarith
    have hprod : 0 ≤ ((y * z) + (z * x) + (x * y)) *
        ((y * z) ^ 2 + (z * x) ^ 2 + (x * y) ^ 2 - (y * z) * (z * x) -
          (y * z) * (x * y) - (z * x) * (x * y)) := mul_nonneg hsum hsq
    nlinarith [hprod]
  field_simp [ne_of_gt hx, ne_of_gt hy, ne_of_gt hz]
  nlinarith [hc]

theorem P12 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ≤ 2) : 6 ≤ 2 * (a * b + 1) / (a + b) ^ 2 + 2 * (b * c + 1) / (b + c) ^ 2 + 2 * (c * a + 1) / (c + a) ^ 2 := by
  have hsym : a ^ 2 + b ^ 2 + c ^ 2 + a * b + a * c + b * c ≤ 2 := by
    nlinarith [h]
  have h1 : 1 + ((b + c) * (c + a)) / (a + b) ^ 2 ≤
      2 * (a * b + 1) / (a + b) ^ 2 := term_bound ha hb hsym
  have hrot1 : b ^ 2 + c ^ 2 + a ^ 2 + b * c + b * a + c * a ≤ 2 := by
    nlinarith [hsym]
  have h2 : 1 + ((c + a) * (a + b)) / (b + c) ^ 2 ≤
      2 * (b * c + 1) / (b + c) ^ 2 := term_bound hb hc hrot1
  have hrot2 : c ^ 2 + a ^ 2 + b ^ 2 + c * a + c * b + a * b ≤ 2 := by
    nlinarith [hsym]
  have h3 : 1 + ((a + b) * (b + c)) / (c + a) ^ 2 ≤
      2 * (c * a + 1) / (c + a) ^ 2 := term_bound hc ha hrot2
  have hcyc : 3 ≤ ((b + c) * (c + a)) / (a + b) ^ 2 +
      ((c + a) * (a + b)) / (b + c) ^ 2 +
        ((a + b) * (b + c)) / (c + a) ^ 2 := by
    exact cyclic_sum_ge_three (add_pos ha hb) (add_pos hb hc) (add_pos hc ha)
  nlinarith [h1, h2, h3, hcyc]
