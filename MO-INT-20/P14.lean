import Mathlib

lemma titu3 (f g : Fin 3 → ℝ) (hg : ∀ i, 0 < g i) :
    (∑ i : Fin 3, f i)^2 / ∑ i : Fin 3, g i ≤ ∑ i : Fin 3, (f i)^2 / g i := by
  have hg' : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 < g i := by
    intro i hi
    exact hg i
  have hT := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin 3)) f hg'
  simpa using hT

lemma P14_aux (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x * y * z = 1) :
    1 / 3 ≤ x ^ 3 / (2 * y + z) ^ 2 + y ^ 3 / (2 * z + x) ^ 2
      + z ^ 3 / (2 * x + y) ^ 2 := by
  let F : Fin 3 → ℝ := fun i => if i = 0 then x ^ 2 / (2 * y + z) else
    if i = 1 then y ^ 2 / (2 * z + x) else z ^ 2 / (2 * x + y)
  let G : Fin 3 → ℝ := fun i => if i = 0 then x else if i = 1 then y else z
  have hGpos : ∀ i, 0 < G i := by
    intro i
    fin_cases i <;> simp [G, hx, hy, hz]
  have hT := titu3 F G hGpos
  have hSumF : (∑ i : Fin 3, F i) =
      x ^ 2 / (2 * y + z) + y ^ 2 / (2 * z + x) + z ^ 2 / (2 * x + y) := by
    rw [Fin.sum_univ_three]
    simp [F]
  have hSumG : (∑ i : Fin 3, G i) = x + y + z := by
    rw [Fin.sum_univ_three]
    simp [G]
  have hSumFG : (∑ i : Fin 3, (F i) ^ 2 / G i) =
      x ^ 3 / (2 * y + z) ^ 2 + y ^ 3 / (2 * z + x) ^ 2
        + z ^ 3 / (2 * x + y) ^ 2 := by
    rw [Fin.sum_univ_three]
    simp [F, G]
    field_simp [hx.ne', hy.ne', hz.ne',
      (show 2 * y + z ≠ 0 by positivity),
      (show 2 * z + x ≠ 0 by positivity),
      (show 2 * x + y ≠ 0 by positivity)]
  have hTitu' :
      (x ^ 2 / (2 * y + z) + y ^ 2 / (2 * z + x) + z ^ 2 / (2 * x + y)) ^ 2
        / (x + y + z) ≤
        x ^ 3 / (2 * y + z) ^ 2 + y ^ 3 / (2 * z + x) ^ 2
          + z ^ 3 / (2 * x + y) ^ 2 := by
    rw [← hSumFG]
    rw [← hSumF, ← hSumG]
    simpa using hT
  let F2 : Fin 3 → ℝ := fun i => if i = 0 then x else if i = 1 then y else z
  let G2 : Fin 3 → ℝ := fun i => if i = 0 then 2 * y + z else
    if i = 1 then 2 * z + x else 2 * x + y
  have hG2pos : ∀ i, 0 < G2 i := by
    intro i
    fin_cases i <;> simp [G2] <;> positivity
  have hT2 := titu3 F2 G2 hG2pos
  have hSumF2 : (∑ i : Fin 3, F2 i) = x + y + z := by
    rw [Fin.sum_univ_three]
    simp [F2]
  have hSumG2 : (∑ i : Fin 3, G2 i) = 3 * (x + y + z) := by
    rw [Fin.sum_univ_three]
    simp [G2]
    ring
  have hSumF2G2 : (∑ i : Fin 3, (F2 i) ^ 2 / G2 i) =
      x ^ 2 / (2 * y + z) + y ^ 2 / (2 * z + x) + z ^ 2 / (2 * x + y) := by
    rw [Fin.sum_univ_three]
    simp [F2, G2]
  have hT2e : (x + y + z) ^ 2 / (3 * (x + y + z))
      ≤ x ^ 2 / (2 * y + z) + y ^ 2 / (2 * z + x) + z ^ 2 / (2 * x + y) := by
    rw [hSumF2, hSumG2, hSumF2G2] at hT2
    exact hT2
  have hNesbitt :
      (x + y + z) / 3 ≤ x ^ 2 / (2 * y + z) + y ^ 2 / (2 * z + x)
        + z ^ 2 / (2 * x + y) := by
    have ht : 0 < x + y + z := by positivity
    have heq : (x + y + z) ^ 2 / (3 * (x + y + z)) = (x + y + z) / 3 := by
      field_simp [ht.ne']
    rw [← heq]
    exact hT2e
  have hAMGM : 3 ≤ x + y + z := by
    have hAMGM' := Real.geom_mean_le_arith_mean3_weighted
        (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
        (p₁ := x) (p₂ := y) (p₃ := z)
        (by norm_num) (by norm_num) (by norm_num)
        hx.le hy.le hz.le (by norm_num)
    have hmul : x ^ (1 / 3 : ℝ) * y ^ (1 / 3 : ℝ) * z ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.mul_rpow hx.le hy.le]
      rw [← Real.mul_rpow (mul_nonneg hx.le hy.le) hz.le]
      rw [hxyz]
      norm_num
    have h1 : 1 ≤ (x + y + z) / 3 := by
      nlinarith [hAMGM', hmul]
    nlinarith
  have htpos : 0 < x + y + z := by positivity
  have hsq : ((x + y + z) / 3) ^ 2
      ≤ (x ^ 2 / (2 * y + z) + y ^ 2 / (2 * z + x) + z ^ 2 / (2 * x + y)) ^ 2 := by
    apply sq_le_sq'
    · nlinarith [hNesbitt, htpos]
    · exact hNesbitt
  have hmid : (((x + y + z) / 3) ^ 2) / (x + y + z) ≤
      x ^ 3 / (2 * y + z) ^ 2 + y ^ 3 / (2 * z + x) ^ 2
        + z ^ 3 / (2 * x + y) ^ 2 := by
    exact le_trans (div_le_div_of_nonneg_right hsq htpos.le) hTitu'
  have hlow : 1 / 3 ≤ (((x + y + z) / 3) ^ 2) / (x + y + z) := by
    have heq : (((x + y + z) / 3) ^ 2) / (x + y + z) = (x + y + z) / 9 := by
      field_simp [htpos.ne']
      ring
    rw [heq]
    nlinarith [hAMGM]
  exact le_trans hlow hmid

theorem P14 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a*b*c = 1) : 1 / (c^5 * (a + 2*b)^2) + 1 / (b^5 * (c + 2*a)^2) + 1 / (a^5 * (b + 2*c)^2) ≥ 1 / 3 := by
  have hxyz : (1/a) * (1/b) * (1/c) = 1 := by
    field_simp [ha.ne', hb.ne', hc.ne']
    nlinarith [h]
  have hS := P14_aux (1/a) (1/b) (1/c) (by positivity) (by positivity)
    (by positivity) hxyz
  have hT3 : 1 / (a^5 * (b + 2*c)^2) =
      (1/a)^3 / (2*(1/b) + (1/c))^2 := by
    have hsq : a ^ 2 * b ^ 2 * c ^ 2 = 1 := by
      rw [show a ^ 2 * b ^ 2 * c ^ 2 = (a * b * c) ^ 2 by ring]
      rw [h]
      norm_num
    field_simp [ha.ne', hb.ne', hc.ne',
      (show b + 2*c ≠ 0 by positivity),
      (show 2*(1/b) + (1/c) ≠ 0 by positivity)]
    rw [hsq]
    ring
  have hT2 : 1 / (b^5 * (c + 2*a)^2) =
      (1/b)^3 / (2*(1/c) + (1/a))^2 := by
    have hsq : b ^ 2 * c ^ 2 * a ^ 2 = 1 := by
      rw [show b ^ 2 * c ^ 2 * a ^ 2 = (a * b * c) ^ 2 by ring]
      rw [h]
      norm_num
    field_simp [ha.ne', hb.ne', hc.ne',
      (show c + 2*a ≠ 0 by positivity),
      (show 2*(1/c) + (1/a) ≠ 0 by positivity)]
    rw [hsq]
    ring
  have hT1 : 1 / (c^5 * (a + 2*b)^2) =
      (1/c)^3 / (2*(1/a) + (1/b))^2 := by
    have hsq : c ^ 2 * a ^ 2 * b ^ 2 = 1 := by
      rw [show c ^ 2 * a ^ 2 * b ^ 2 = (a * b * c) ^ 2 by ring]
      rw [h]
      norm_num
    field_simp [ha.ne', hb.ne', hc.ne',
      (show a + 2*b ≠ 0 by positivity),
      (show 2*(1/a) + (1/b) ≠ 0 by positivity)]
    rw [hsq]
    ring
  rw [hT1, hT2, hT3]
  simpa [add_comm, add_left_comm, add_assoc] using hS
