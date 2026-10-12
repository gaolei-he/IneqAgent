import Mathlib

theorem P37 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a ^ 3 + b ^ 3 + c ^ 3 + a * b * c = 4) : (10 - a * b * c) ^ 2 / (a + b + c) ≤ (5 * a ^ 2 + b * c) ^ 2 / ((a + b) * (a + c)) + (5 * b ^ 2 + c * a) ^ 2 / ((b + c) * (b + a)) + (5 * c ^ 2 + a * b)^2 / ((c + a) * (c + b)) := by
  -- The Engel form of Cauchy-Schwarz applied to scaled sequences f and g.
  -- The scaling factors (a/2), (b/2), (c/2) are chosen so that the sums of
  -- f and g simplify to the numerator and denominator on the left, using h.
  let f : Fin 3 → ℝ := fun i =>
    ![(a / 2) * (5 * a ^ 2 + b * c),
      (b / 2) * (5 * b ^ 2 + c * a),
      (c / 2) * (5 * c ^ 2 + a * b)] i
  let g : Fin 3 → ℝ := fun i =>
    ![(a / 2) ^ 2 * ((a + b) * (a + c)),
      (b / 2) ^ 2 * ((b + c) * (b + a)),
      (c / 2) ^ 2 * ((c + a) * (c + b))] i
  have hposg : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 < g i := by
    intro i _hi
    fin_cases i <;> dsimp [g] <;> positivity
  have hengel_raw :=
    Finset.sq_sum_div_le_sum_sq_div (s := Finset.univ) (f := f) (g := g) hposg
  have hsum_f : (∑ i : Fin 3, f i) = 10 - a * b * c := by
    simp [f, Fin.sum_univ_three]
    nlinarith [h]
  have hsum_g : (∑ i : Fin 3, g i) = a + b + c := by
    have hmul :
        4 * (∑ i : Fin 3, g i) =
          (a + b + c) * (a ^ 3 + b ^ 3 + c ^ 3 + a * b * c) := by
      simp [g, Fin.sum_univ_three]
      ring
    nlinarith [hmul, h]
  have hterm1 :
      f 0 ^ 2 / g 0 =
        (5 * a ^ 2 + b * c) ^ 2 / ((a + b) * (a + c)) := by
    dsimp [f, g]
    field_simp [ha.ne']
  have hterm2 :
      f 1 ^ 2 / g 1 =
        (5 * b ^ 2 + c * a) ^ 2 / ((b + c) * (b + a)) := by
    dsimp [f, g]
    field_simp [hb.ne']
  have hterm3 :
      f 2 ^ 2 / g 2 =
        (5 * c ^ 2 + a * b) ^ 2 / ((c + a) * (c + b)) := by
    dsimp [f, g]
    field_simp [hc.ne']
  calc
    (10 - a * b * c) ^ 2 / (a + b + c) =
        (∑ i : Fin 3, f i) ^ 2 / (∑ i : Fin 3, g i) := by
      rw [hsum_f, hsum_g]
    _ ≤ ∑ i : Fin 3, f i ^ 2 / g i := hengel_raw
    _ =
        (5 * a ^ 2 + b * c) ^ 2 / ((a + b) * (a + c)) +
          (5 * b ^ 2 + c * a) ^ 2 / ((b + c) * (b + a)) +
            (5 * c ^ 2 + a * b) ^ 2 / ((c + a) * (c + b)) := by
      simp [Fin.sum_univ_three, hterm1, hterm2, hterm3]
