import Mathlib

open Real

local notation "sqrt" => Real.sqrt

/-- Three-term Cauchy-Schwarz inequality over the reals. -/
lemma cauchy3 (x1 x2 x3 y1 y2 y3 : ℝ) :
    (x1 * y1 + x2 * y2 + x3 * y3) ^ 2 ≤
      (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) := by
  have h :
      (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) * (y1 ^ 2 + y2 ^ 2 + y3 ^ 2) -
          (x1 * y1 + x2 * y2 + x3 * y3) ^ 2 =
        (x1 * y2 - x2 * y1) ^ 2 + (x1 * y3 - x3 * y1) ^ 2 +
          (x2 * y3 - x3 * y2) ^ 2 := by
    ring
  nlinarith [h, sq_nonneg (x1 * y2 - x2 * y1), sq_nonneg (x1 * y3 - x3 * y1),
    sq_nonneg (x2 * y3 - x3 * y2)]

/-- Algebraic core of the proof: `a^3 + b^3 + c^3 + 24abc ≤ (a + b + c)^3`
for nonnegative `a`, `b`, `c`. -/
lemma cube_bound {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a ^ 3 + b ^ 3 + c ^ 3 + 24 * a * b * c ≤ (a + b + c) ^ 3 := by
  have h :
      (a + b + c) ^ 3 =
        a ^ 3 + b ^ 3 + c ^ 3 + 24 * a * b * c +
          3 * a * (b - c) ^ 2 + 3 * b * (c - a) ^ 2 + 3 * c * (a - b) ^ 2 := by
    ring
  have h1 : 0 ≤ 3 * a * (b - c) ^ 2 := by positivity
  have h2 : 0 ≤ 3 * b * (c - a) ^ 2 := by positivity
  have h3 : 0 ≤ 3 * c * (a - b) ^ 2 := by positivity
  rw [h]
  nlinarith

/-- Titu's lemma for three terms with square-root denominators. -/
lemma titu3 {a b c d1 d2 d3 : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) :
    (a + b + c)^2 / (a * sqrt d1 + b * sqrt d2 + c * sqrt d3) ≤
      a / sqrt d1 + b / sqrt d2 + c / sqrt d3 := by
  let f : Fin 3 → ℝ := ![a, b, c]
  let g : Fin 3 → ℝ := ![a * sqrt d1, b * sqrt d2, c * sqrt d3]
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 < g i := by
    intro i hi
    fin_cases i <;> simp [g] <;> positivity
  have ht := Finset.sq_sum_div_le_sum_sq_div (R := ℝ) (s := (Finset.univ : Finset (Fin 3)))
      (f := f) (g := g) hg
  have ht' : (a + b + c)^2 / (a * sqrt d1 + b * sqrt d2 + c * sqrt d3) ≤
      a^2 / (a * sqrt d1) + b^2 / (b * sqrt d2) + c^2 / (c * sqrt d3) := by
    simpa [Fin.sum_univ_three, f, g] using ht
  have hcancel : a^2 / (a * sqrt d1) + b^2 / (b * sqrt d2) + c^2 / (c * sqrt d3) =
      a / sqrt d1 + b / sqrt d2 + c / sqrt d3 := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc,
      (Real.sqrt_pos.2 hd1).ne', (Real.sqrt_pos.2 hd2).ne', (Real.sqrt_pos.2 hd3).ne']
  rwa [hcancel] at ht'

/-- Cauchy-Schwarz bound on the weighted sum of square roots. -/
lemma cs_bound {a b c d1 d2 d3 : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hd3 : 0 < d3) :
    (a * sqrt d1 + b * sqrt d2 + c * sqrt d3) ^ 2 ≤
      (a + b + c) * (a * d1 + b * d2 + c * d3) := by
  have hC := cauchy3 (sqrt a) (sqrt b) (sqrt c)
    (sqrt (a * d1)) (sqrt (b * d2)) (sqrt (c * d3))
  have hp1 : sqrt a * sqrt (a * d1) = a * sqrt d1 := by
    rw [Real.sqrt_mul (le_of_lt ha) d1, ← mul_assoc, Real.mul_self_sqrt (le_of_lt ha)]
  have hp2 : sqrt b * sqrt (b * d2) = b * sqrt d2 := by
    rw [Real.sqrt_mul (le_of_lt hb) d2, ← mul_assoc, Real.mul_self_sqrt (le_of_lt hb)]
  have hp3 : sqrt c * sqrt (c * d3) = c * sqrt d3 := by
    rw [Real.sqrt_mul (le_of_lt hc) d3, ← mul_assoc, Real.mul_self_sqrt (le_of_lt hc)]
  have hsq1 : (sqrt a) ^ 2 = a := Real.sq_sqrt (le_of_lt ha)
  have hsq2 : (sqrt b) ^ 2 = b := Real.sq_sqrt (le_of_lt hb)
  have hsq3 : (sqrt c) ^ 2 = c := Real.sq_sqrt (le_of_lt hc)
  have hq1 : (sqrt (a * d1)) ^ 2 = a * d1 := Real.sq_sqrt (mul_nonneg (le_of_lt ha) (le_of_lt hd1))
  have hq2 : (sqrt (b * d2)) ^ 2 = b * d2 := Real.sq_sqrt (mul_nonneg (le_of_lt hb) (le_of_lt hd2))
  have hq3 : (sqrt (c * d3)) ^ 2 = c * d3 := Real.sq_sqrt (mul_nonneg (le_of_lt hc) (le_of_lt hd3))
  simpa [hp1, hp2, hp3, hsq1, hsq2, hsq3, hq1, hq2, hq3, mul_assoc] using hC

theorem P21 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 ≤ a / sqrt (a ^ 2 + 8 * b * c) + b / sqrt (b ^ 2 + 8 * a * c) + c / sqrt (c ^ 2 + 8 * a * b) := by
  have hd1 : 0 < a ^ 2 + 8 * b * c := by positivity
  have hd2 : 0 < b ^ 2 + 8 * a * c := by positivity
  have hd3 : 0 < c ^ 2 + 8 * a * b := by positivity
  have hs : 0 < a + b + c := by positivity
  have hden : 0 < a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
      c * sqrt (c ^ 2 + 8 * a * b) := by
    positivity
  have htitu := titu3 ha hb hc hd1 hd2 hd3
  have hcs := cs_bound ha hb hc hd1 hd2 hd3
  have hY : a * (a ^ 2 + 8 * b * c) + b * (b ^ 2 + 8 * a * c) +
      c * (c ^ 2 + 8 * a * b) = a ^ 3 + b ^ 3 + c ^ 3 + 24 * a * b * c := by
    ring
  have hYle : a * (a ^ 2 + 8 * b * c) + b * (b ^ 2 + 8 * a * c) +
      c * (c ^ 2 + 8 * a * b) ≤ (a + b + c) ^ 3 := by
    rw [hY]
    exact cube_bound (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
  have hT2le : (a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
      c * sqrt (c ^ 2 + 8 * a * b)) ^ 2 ≤ (a + b + c) ^ 4 := by
    have hstep : (a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
        c * sqrt (c ^ 2 + 8 * a * b)) ^ 2 ≤
        (a + b + c) * (a * (a ^ 2 + 8 * b * c) + b * (b ^ 2 + 8 * a * c) +
          c * (c ^ 2 + 8 * a * b)) := hcs
    have hYmul : (a + b + c) * (a * (a ^ 2 + 8 * b * c) + b * (b ^ 2 + 8 * a * c) +
        c * (c ^ 2 + 8 * a * b)) ≤ (a + b + c) * (a + b + c) ^ 3 :=
      mul_le_mul_of_nonneg_left hYle (le_of_lt hs)
    calc
      _ ≤ _ := hstep
      _ ≤ _ := hYmul
      _ = (a + b + c) ^ 4 := by ring
  have hTle : a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
      c * sqrt (c ^ 2 + 8 * a * b) ≤ (a + b + c) ^ 2 := by
    have h2 : (a + b + c) ^ 4 = ((a + b + c) ^ 2) ^ 2 := by ring
    have hnn1 : 0 ≤ a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
        c * sqrt (c ^ 2 + 8 * a * b) := by positivity
    have hnn2 : 0 ≤ (a + b + c) ^ 2 := by positivity
    have h2' : (a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
        c * sqrt (c ^ 2 + 8 * a * b)) ^ 2 ≤ ((a + b + c) ^ 2) ^ 2 := by
      rw [← h2]
      exact hT2le
    have habs := sq_le_sq.mp h2'
    simpa [abs_of_nonneg hnn1, abs_of_nonneg hnn2] using habs
  have h1le : 1 ≤ (a + b + c) ^ 2 /
      (a * sqrt (a ^ 2 + 8 * b * c) + b * sqrt (b ^ 2 + 8 * a * c) +
        c * sqrt (c ^ 2 + 8 * a * b)) :=
    (one_le_div hden).2 hTle
  exact le_trans h1le htitu
