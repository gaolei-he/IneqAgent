import Mathlib

theorem real_p4 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : √(a^2 + a*b + b^2) + √(b^2 + b*c + c^2) + √(c^2 + c*a + a^2) ≤ √(5 * (a^2 + b^2 + c^2) + 4 * (a*b + b*c + c*a)) := by
  have ha0 : 0 ≤ a := le_of_lt ha
  have hb0 : 0 ≤ b := le_of_lt hb
  have hc0 : 0 ≤ c := le_of_lt hc
  have hq_ab0 : 0 ≤ a ^ 2 + a * b + b ^ 2 := by positivity
  have hq_bc0 : 0 ≤ b ^ 2 + b * c + c ^ 2 := by positivity
  have hq_ca0 : 0 ≤ c ^ 2 + c * a + a ^ 2 := by positivity
  have hpair : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hsum_sq_nonneg : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a) := by
    exact sub_nonneg.mpr hpair
  have htarget_decomp :
      5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a) =
        3 * (a + b + c) ^ 2 +
          2 * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by
    ring
  have hsum_pos : 0 < a + b + c := by
    linarith
  have htarget0 : 0 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a) := by
    rw [htarget_decomp]
    positivity
  let x := √(a ^ 2 + a * b + b ^ 2)
  let y := √(b ^ 2 + b * c + c ^ 2)
  let z := √(c ^ 2 + c * a + a ^ 2)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := by
    dsimp [z]
    exact Real.sqrt_nonneg _
  have hleft0 : 0 ≤ x + y + z := by
    nlinarith
  have hx_sq : x ^ 2 = a ^ 2 + a * b + b ^ 2 := by
    dsimp [x]
    exact Real.sq_sqrt hq_ab0
  have hy_sq : y ^ 2 = b ^ 2 + b * c + c ^ 2 := by
    dsimp [y]
    exact Real.sq_sqrt hq_bc0
  have hz_sq : z ^ 2 = c ^ 2 + c * a + a ^ 2 := by
    dsimp [z]
    exact Real.sq_sqrt hq_ca0
  have hleft_sq_expand :
      (x + y + z) ^ 2 =
        2 * (a ^ 2 + b ^ 2 + c ^ 2) + (a * b + b * c + c * a) +
          2 * (x * y + y * z + z * x) := by
    calc
      (x + y + z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * (x * y + y * z + z * x) := by
        ring
      _ = 2 * (a ^ 2 + b ^ 2 + c ^ 2) + (a * b + b * c + c * a) +
          2 * (x * y + y * z + z * x) := by
        rw [hx_sq, hy_sq, hz_sq]
        ring
  have hsq_goal_of_cross :
      2 * (x * y + y * z + z * x) ≤
          3 * (a ^ 2 + b ^ 2 + c ^ 2) + 3 * (a * b + b * c + c * a) →
        (x + y + z) ^ 2 ≤
          5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a) := by
    intro hcross
    rw [hleft_sq_expand]
    nlinarith
  have hle_sqrt_of_sq :
      (x + y + z) ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a) →
        x + y + z ≤ √(5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a)) := by
    intro hsq
    have hright0 :
        0 ≤ √(5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a)) := by
      exact Real.sqrt_nonneg _
    have hsq' :
        (x + y + z) ^ 2 ≤
          (√(5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a))) ^ 2 := by
      simpa [Real.sq_sqrt htarget0] using hsq
    have habs :
        |x + y + z| ≤
          |√(5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a))| := by
      exact sq_le_sq.mp hsq'
    rwa [abs_of_nonneg hleft0, abs_of_nonneg hright0] at habs
  have h_cauchy3 (u₁ u₂ u₃ v₁ v₂ v₃ : ℝ) :
      (u₁ * v₁ + u₂ * v₂ + u₃ * v₃) ^ 2 ≤
        (u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2) * (v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) := by
    nlinarith [sq_nonneg (u₁ * v₂ - u₂ * v₁),
      sq_nonneg (u₁ * v₃ - u₃ * v₁), sq_nonneg (u₂ * v₃ - u₃ * v₂)]
  have hab_pos : 0 < a + b := by linarith
  have hbc_pos : 0 < b + c := by linarith
  have hca_pos : 0 < c + a := by linarith
  have hsqrt_ab_sq : (√(a + b)) ^ 2 = a + b := by
    exact Real.sq_sqrt (le_of_lt hab_pos)
  have hsqrt_bc_sq : (√(b + c)) ^ 2 = b + c := by
    exact Real.sq_sqrt (le_of_lt hbc_pos)
  have hsqrt_ca_sq : (√(c + a)) ^ 2 = c + a := by
    exact Real.sq_sqrt (le_of_lt hca_pos)
  have hx_weight : √(a + b) * (x / √(a + b)) = x := by
    have hsqrt_ne : √(a + b) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hab_pos)
    field_simp [hsqrt_ne]
  have hy_weight : √(b + c) * (y / √(b + c)) = y := by
    have hsqrt_ne : √(b + c) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hbc_pos)
    field_simp [hsqrt_ne]
  have hz_weight : √(c + a) * (z / √(c + a)) = z := by
    have hsqrt_ne : √(c + a) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hca_pos)
    field_simp [hsqrt_ne]
  have hx_div_sq : (x / √(a + b)) ^ 2 = x ^ 2 / (a + b) := by
    rw [div_pow, hsqrt_ab_sq]
  have hy_div_sq : (y / √(b + c)) ^ 2 = y ^ 2 / (b + c) := by
    rw [div_pow, hsqrt_bc_sq]
  have hz_div_sq : (z / √(c + a)) ^ 2 = z ^ 2 / (c + a) := by
    rw [div_pow, hsqrt_ca_sq]
  have hleft_weighted_sq :
      (x + y + z) ^ 2 ≤
        ((a + b) + (b + c) + (c + a)) *
          (x ^ 2 / (a + b) + y ^ 2 / (b + c) + z ^ 2 / (c + a)) := by
    calc
      (x + y + z) ^ 2 =
          (√(a + b) * (x / √(a + b)) +
            √(b + c) * (y / √(b + c)) +
            √(c + a) * (z / √(c + a))) ^ 2 := by
        rw [hx_weight, hy_weight, hz_weight]
      _ ≤
          ((√(a + b)) ^ 2 + (√(b + c)) ^ 2 + (√(c + a)) ^ 2) *
            ((x / √(a + b)) ^ 2 + (y / √(b + c)) ^ 2 +
              (z / √(c + a)) ^ 2) := by
        exact h_cauchy3 (√(a + b)) (√(b + c)) (√(c + a))
          (x / √(a + b)) (y / √(b + c)) (z / √(c + a))
      _ =
          ((a + b) + (b + c) + (c + a)) *
            (x ^ 2 / (a + b) + y ^ 2 / (b + c) + z ^ 2 / (c + a)) := by
        rw [hsqrt_ab_sq, hsqrt_bc_sq, hsqrt_ca_sq, hx_div_sq, hy_div_sq, hz_div_sq]
  have hleft_weighted_rad :
      (x + y + z) ^ 2 ≤
        2 * (a + b + c) *
          ((a ^ 2 + a * b + b ^ 2) / (a + b) +
            (b ^ 2 + b * c + c ^ 2) / (b + c) +
            (c ^ 2 + c * a + a ^ 2) / (c + a)) := by
    calc
      (x + y + z) ^ 2 ≤
          ((a + b) + (b + c) + (c + a)) *
            (x ^ 2 / (a + b) + y ^ 2 / (b + c) + z ^ 2 / (c + a)) :=
        hleft_weighted_sq
      _ =
          2 * (a + b + c) *
            ((a ^ 2 + a * b + b ^ 2) / (a + b) +
              (b ^ 2 + b * c + c ^ 2) / (b + c) +
              (c ^ 2 + c * a + a ^ 2) / (c + a)) := by
        rw [hx_sq, hy_sq, hz_sq]
        ring
  have hweighted_rational_bound :
      2 * (a + b + c) *
          ((a ^ 2 + a * b + b ^ 2) / (a + b) +
            (b ^ 2 + b * c + c ^ 2) / (b + c) +
            (c ^ 2 + c * a + a ^ 2) / (c + a)) ≤
        5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a) := by
    have hden_pos : 0 < (a + b) * (b + c) * (c + a) := by positivity
    have hnum_decomp :
        a ^ 4 * b + a ^ 4 * c - a ^ 3 * b ^ 2 - a ^ 3 * c ^ 2 -
              a ^ 2 * b ^ 3 - a ^ 2 * c ^ 3 + a * b ^ 4 + a * c ^ 4 +
              b ^ 4 * c - b ^ 3 * c ^ 2 - b ^ 2 * c ^ 3 + b * c ^ 4 =
            (a - b) ^ 2 * a * b * (a + b) +
              (b - c) ^ 2 * b * c * (b + c) +
              (c - a) ^ 2 * c * a * (c + a) := by
      ring
    have hnum_nonneg :
        0 ≤
          a ^ 4 * b + a ^ 4 * c - a ^ 3 * b ^ 2 - a ^ 3 * c ^ 2 -
            a ^ 2 * b ^ 3 - a ^ 2 * c ^ 3 + a * b ^ 4 + a * c ^ 4 +
            b ^ 4 * c - b ^ 3 * c ^ 2 - b ^ 2 * c ^ 3 + b * c ^ 4 := by
      rw [hnum_decomp]
      positivity
    have hcleared_id :
        ((5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a)) -
              2 * (a + b + c) *
                ((a ^ 2 + a * b + b ^ 2) / (a + b) +
                  (b ^ 2 + b * c + c ^ 2) / (b + c) +
                  (c ^ 2 + c * a + a ^ 2) / (c + a))) *
            ((a + b) * (b + c) * (c + a)) =
          a ^ 4 * b + a ^ 4 * c - a ^ 3 * b ^ 2 - a ^ 3 * c ^ 2 -
            a ^ 2 * b ^ 3 - a ^ 2 * c ^ 3 + a * b ^ 4 + a * c ^ 4 +
            b ^ 4 * c - b ^ 3 * c ^ 2 - b ^ 2 * c ^ 3 + b * c ^ 4 := by
      field_simp [ne_of_gt hab_pos, ne_of_gt hbc_pos, ne_of_gt hca_pos]
      ring
    have hdiff_nonneg :
        0 ≤
          (5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a)) -
            2 * (a + b + c) *
              ((a ^ 2 + a * b + b ^ 2) / (a + b) +
                (b ^ 2 + b * c + c ^ 2) / (b + c) +
                (c ^ 2 + c * a + a ^ 2) / (c + a)) := by
      have hmul_nonneg :
          0 ≤
            ((5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a)) -
                2 * (a + b + c) *
                  ((a ^ 2 + a * b + b ^ 2) / (a + b) +
                    (b ^ 2 + b * c + c ^ 2) / (b + c) +
                    (c ^ 2 + c * a + a ^ 2) / (c + a))) *
              ((a + b) * (b + c) * (c + a)) := by
        rw [hcleared_id]
        exact hnum_nonneg
      exact nonneg_of_mul_nonneg_left hmul_nonneg hden_pos
    exact sub_nonneg.mp hdiff_nonneg
  have hsq_goal :
      (x + y + z) ^ 2 ≤
        5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a) :=
    le_trans hleft_weighted_rad hweighted_rational_bound
  have hxyz_goal :
      x + y + z ≤
        √(5 * (a ^ 2 + b ^ 2 + c ^ 2) + 4 * (a * b + b * c + c * a)) :=
    hle_sqrt_of_sq hsq_goal
  simpa [x, y, z] using hxyz_goal
