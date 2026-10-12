import Mathlib

lemma real_p8_frac_decomp (x : ℝ) (hx : x > 0) :
    (x + 2) / ((x + 1) * (x + 5)) =
      (1 / 4 : ℝ) * (1 / (x + 1) + 3 / (x + 5)) := by
  have hx1 : x + 1 ≠ 0 := by linarith
  have hx5 : x + 5 ≠ 0 := by linarith
  field_simp [hx1, hx5]
  ring

lemma real_p8_cyclic_decomp (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (a + 1) * (b + 2) / ((b + 1) * (b + 5)) +
      (b + 1) * (c + 2) / ((c + 1) * (c + 5)) +
      (c + 1) * (a + 2) / ((a + 1) * (a + 5)) =
      (1 / 4 : ℝ) * ((a + 1) / (b + 1) + (b + 1) / (c + 1) + (c + 1) / (a + 1)) +
      (3 / 4 : ℝ) * ((a + 1) / (b + 5) + (b + 1) / (c + 5) + (c + 1) / (a + 5)) := by
  have hbdec := real_p8_frac_decomp b hb
  have hcdec := real_p8_frac_decomp c hc
  have hadec := real_p8_frac_decomp a ha
  calc
    (a + 1) * (b + 2) / ((b + 1) * (b + 5)) +
        (b + 1) * (c + 2) / ((c + 1) * (c + 5)) +
        (c + 1) * (a + 2) / ((a + 1) * (a + 5))
        = (a + 1) * ((b + 2) / ((b + 1) * (b + 5))) +
          (b + 1) * ((c + 2) / ((c + 1) * (c + 5))) +
          (c + 1) * ((a + 2) / ((a + 1) * (a + 5))) := by
      ring
    _ = (a + 1) * ((1 / 4 : ℝ) * (1 / (b + 1) + 3 / (b + 5))) +
          (b + 1) * ((1 / 4 : ℝ) * (1 / (c + 1) + 3 / (c + 5))) +
          (c + 1) * ((1 / 4 : ℝ) * (1 / (a + 1) + 3 / (a + 5))) := by
      rw [hbdec, hcdec, hadec]
    _ = (1 / 4 : ℝ) * ((a + 1) / (b + 1) + (b + 1) / (c + 1) + (c + 1) / (a + 1)) +
          (3 / 4 : ℝ) * ((a + 1) / (b + 5) + (b + 1) / (c + 5) + (c + 1) / (a + 5)) := by
      ring

lemma real_p8_ratio_sum_ge_three (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (a + 1) / (b + 1) + (b + 1) / (c + 1) + (c + 1) / (a + 1) ≥ 3 := by
  let A : ℝ := a + 1
  let B : ℝ := b + 1
  let C : ℝ := c + 1
  have hA : A > 0 := by dsimp [A]; linarith
  have hB : B > 0 := by dsimp [B]; linarith
  have hC : C > 0 := by dsimp [C]; linarith
  have hA0 : 0 ≤ A := le_of_lt hA
  have hB0 : 0 ≤ B := le_of_lt hB
  have hC0 : 0 ≤ C := le_of_lt hC
  have hprod : (A / B) * (B / C) * (C / A) = 1 := by
    field_simp [ne_of_gt hA, ne_of_gt hB, ne_of_gt hC]
  have hcube :
      (A / B) ^ (1 / 3 : ℝ) * (B / C) ^ (1 / 3 : ℝ) * (C / A) ^ (1 / 3 : ℝ) = 1 := by
    rw [← Real.mul_rpow (div_nonneg hA0 (le_of_lt hB)) (div_nonneg hB0 (le_of_lt hC))]
    rw [← Real.mul_rpow (mul_nonneg (div_nonneg hA0 (le_of_lt hB)) (div_nonneg hB0 (le_of_lt hC))) (div_nonneg hC0 (le_of_lt hA))]
    rw [hprod]
    exact Real.one_rpow (1 / 3 : ℝ)
  have ham := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := 1/3) (w₂ := 1/3) (w₃ := 1/3)
    (p₁ := A/B) (p₂ := B/C) (p₃ := C/A)
    (by norm_num : 0 ≤ (1/3 : ℝ))
    (by norm_num : 0 ≤ (1/3 : ℝ))
    (by norm_num : 0 ≤ (1/3 : ℝ))
    (by positivity : 0 ≤ A/B)
    (by positivity : 0 ≤ B/C)
    (by positivity : 0 ≤ C/A)
    (by norm_num : (1/3:ℝ)+(1/3)+(1/3)=1)
  have hineq : (1/3:ℝ) * (A/B) + (1/3:ℝ) * (B/C) + (1/3:ℝ) * (C/A) ≥ 1 := by
    calc
      1 = (A / B) ^ (1 / 3 : ℝ) * (B / C) ^ (1 / 3 : ℝ) * (C / A) ^ (1 / 3 : ℝ) := hcube.symm
      _ ≤ (1/3:ℝ) * (A / B) + (1/3:ℝ) * (B / C) + (1/3:ℝ) * (C / A) := ham
  have hsum_ge : A / B + B / C + C / A ≥ 3 := by
    nlinarith
  simpa [A, B, C] using hsum_ge

lemma real_p8_single_gap (x y : ℝ) (hy : y > 0) :
    (x + 1) * (y + 2) / ((y + 1) * (y + 5)) - 1 / 2 =
      (2 * (y + 2) * (x - y) + y^2 - 1) / (2 * ((y + 1) * (y + 5))) := by
  have hy1 : y + 1 ≠ 0 := by linarith
  have hy5 : y + 5 ≠ 0 := by linarith
  field_simp [hy1, hy5]
  ring

lemma real_p8_titu3 (x y z : ℝ) (w1 w2 w3 : ℝ) (hw1 : 0 < w1) (hw2 : 0 < w2)
    (hw3 : 0 < w3) :
    (x + y + z)^2 / (w1 + w2 + w3) ≤ x^2 / w1 + y^2 / w2 + z^2 / w3 := by
  let f : Fin 3 → ℝ := ![x, y, z]
  let g : Fin 3 → ℝ := ![w1, w2, w3]
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 < g i := by
    intro i hi
    fin_cases i <;> simp [g] <;> assumption
  have hmain := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin 3)) f hg
  have hsumf : (∑ i : Fin 3, f i) = x + y + z := by
    dsimp [f]
    simp only [Fin.sum_univ_succ]
    simp [add_assoc]
  have hsumg : (∑ i : Fin 3, g i) = w1 + w2 + w3 := by
    dsimp [g]
    simp only [Fin.sum_univ_succ]
    simp [add_assoc]
  have hsumsq : (∑ i : Fin 3, f i ^ 2 / g i) = x ^ 2 / w1 + y ^ 2 / w2 + z ^ 2 / w3 := by
    dsimp [f, g]
    simp only [Fin.sum_univ_succ]
    simp [add_assoc]
  rwa [hsumf, hsumg, hsumsq] at hmain

lemma real_p8_ratio_bound (x : ℝ) (hx : x > 0) :
    (x + 1) * (x + 5) / (x + 2) ≤ (4 * x + 8) / 3 := by
  have hx2_ne : x + 2 ≠ 0 := by linarith
  have h3_ne : (3 : ℝ) ≠ 0 := by norm_num
  field_simp [hx2_ne, h3_ne]
  nlinarith [sq_nonneg (x - 1)]

lemma real_p8_denom_sum_bound (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    (a + 1) * ((b + 1) * (b + 5) / (b + 2)) +
        (b + 1) * ((c + 1) * (c + 5) / (c + 2)) +
        (c + 1) * ((a + 1) * (a + 5) / (a + 2)) ≤
      (4 / 3 : ℝ) * (a * b + b * c + c * a + 3 * (a + b + c) + 6) := by
  have hb := real_p8_ratio_bound b hb
  have hc := real_p8_ratio_bound c hc
  have ha := real_p8_ratio_bound a ha
  have hb' : (a + 1) * ((b + 1) * (b + 5) / (b + 2)) ≤ (a + 1) * ((4 * b + 8) / 3) := by
    exact mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ a + 1)
  have hc' : (b + 1) * ((c + 1) * (c + 5) / (c + 2)) ≤ (b + 1) * ((4 * c + 8) / 3) := by
    exact mul_le_mul_of_nonneg_left hc (by linarith : 0 ≤ b + 1)
  have ha' : (c + 1) * ((a + 1) * (a + 5) / (a + 2)) ≤ (c + 1) * ((4 * a + 8) / 3) := by
    exact mul_le_mul_of_nonneg_left ha (by linarith : 0 ≤ c + 1)
  have hsum :
      (a + 1) * ((b + 1) * (b + 5) / (b + 2)) +
          (b + 1) * ((c + 1) * (c + 5) / (c + 2)) +
          (c + 1) * ((a + 1) * (a + 5) / (a + 2)) ≤
        (a + 1) * ((4 * b + 8) / 3) +
          (b + 1) * ((4 * c + 8) / 3) +
          (c + 1) * ((4 * a + 8) / 3) := by
    linarith
  have hrewrite :
      (a + 1) * ((4 * b + 8) / 3) +
          (b + 1) * ((4 * c + 8) / 3) +
          (c + 1) * ((4 * a + 8) / 3) =
        (4 / 3 : ℝ) * (a * b + b * c + c * a + 3 * (a + b + c) + 6) := by
    ring
  rw [hrewrite] at hsum
  exact hsum

theorem real_p8 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a^2 + b^2 + c^2 ≥ 3) : (a + 1) * (b + 2) / ((b + 1) * (b + 5)) + (b + 1) * (c + 2) / ((c + 1) * (c + 5)) + (c + 1) * (a + 2) / ((a + 1) * (a + 5)) ≥ 3 / 2 := by
  let W1 : ℝ := (a + 1) * ((b + 1) * (b + 5) / (b + 2))
  let W2 : ℝ := (b + 1) * ((c + 1) * (c + 5) / (c + 2))
  let W3 : ℝ := (c + 1) * ((a + 1) * (a + 5) / (a + 2))
  have hW1_pos : 0 < W1 := by dsimp [W1]; positivity
  have hW2_pos : 0 < W2 := by dsimp [W2]; positivity
  have hW3_pos : 0 < W3 := by dsimp [W3]; positivity
  have hcauchy0 := real_p8_titu3 (a + 1) (b + 1) (c + 1) W1 W2 W3 hW1_pos hW2_pos hW3_pos
  have hnum : (a + 1) + (b + 1) + (c + 1) = a + b + c + 3 := by ring
  have hcauchy :
      (a + b + c + 3)^2 / (W1 + W2 + W3) ≤
        (a + 1)^2 / W1 + (b + 1)^2 / W2 + (c + 1)^2 / W3 := by
    rwa [hnum] at hcauchy0
  have hsum_rw :
      (a + 1)^2 / W1 + (b + 1)^2 / W2 + (c + 1)^2 / W3 =
        (a + 1) * (b + 2) / ((b + 1) * (b + 5)) +
          (b + 1) * (c + 2) / ((c + 1) * (c + 5)) +
          (c + 1) * (a + 2) / ((a + 1) * (a + 5)) := by
    have hb2_ne : b + 2 ≠ 0 := by linarith
    have hc2_ne : c + 2 ≠ 0 := by linarith
    have ha2_ne : a + 2 ≠ 0 := by linarith
    have hb1_ne : b + 1 ≠ 0 := by linarith
    have hc1_ne : c + 1 ≠ 0 := by linarith
    have ha1_ne : a + 1 ≠ 0 := by linarith
    have hb5_ne : b + 5 ≠ 0 := by linarith
    have hc5_ne : c + 5 ≠ 0 := by linarith
    have ha5_ne : a + 5 ≠ 0 := by linarith
    dsimp [W1, W2, W3]
    field_simp [ha1_ne, ha2_ne, hb1_ne, hb2_ne, hb5_ne, hc1_ne, hc2_ne, hc5_ne, ha5_ne]
  have hden_bound := real_p8_denom_sum_bound a b c ha hb hc
  have hden_bound' :
      W1 + W2 + W3 ≤ (2 / 3 : ℝ) * (a + b + c + 3)^2 := by
    have hmiddle :
        (4 / 3 : ℝ) * (a * b + b * c + c * a + 3 * (a + b + c) + 6) ≤
          (2 / 3 : ℝ) * (a + b + c + 3)^2 := by
      have hid :
          (2 / 3 : ℝ) * (a + b + c + 3)^2 -
              (4 / 3 : ℝ) * (a * b + b * c + c * a + 3 * (a + b + c) + 6) =
            (2 / 3 : ℝ) * (a^2 + b^2 + c^2 - 3) := by
        ring
      nlinarith [hid, h]
    have hsum' : W1 + W2 + W3 ≤ (4 / 3 : ℝ) * (a * b + b * c + c * a + 3 * (a + b + c) + 6) := by
      dsimp [W1, W2, W3]
      exact hden_bound
    exact le_trans hsum' hmiddle
  have hD_pos : 0 < W1 + W2 + W3 := by positivity
  have hfrac_ge : (3 / 2 : ℝ) ≤ (a + b + c + 3)^2 / (W1 + W2 + W3) := by
    rw [le_div_iff₀ hD_pos]
    nlinarith [hden_bound']
  have hS_ge : (3 / 2 : ℝ) ≤
      (a + 1) * (b + 2) / ((b + 1) * (b + 5)) +
        (b + 1) * (c + 2) / ((c + 1) * (c + 5)) +
        (c + 1) * (a + 2) / ((a + 1) * (a + 5)) := by
    rw [← hsum_rw]
    exact le_trans hfrac_ge hcauchy
  exact hS_ge
