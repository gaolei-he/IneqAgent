import Mathlib

theorem real_p16 (n : ℕ) (hn : n > 0) (a b : Fin n → ℝ) : (∑ i : Fin n, (a i * b i)) + √((∑ i : Fin n, (a i)^2) * (∑ i : Fin n, (b i)^2)) ≥ 2 / n * (∑ i : Fin n, a i) * (∑ i : Fin n, b i) := by
  classical
  -- Work with the real cast of n so that division behaves as expected.
  have hn_real_pos : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hn_real_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
  -- The two norm-squared sums are nonnegative, so we may split the square root.
  have hsq_a_nonneg : 0 ≤ ∑ i : Fin n, (a i) ^ 2 := by
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (a i))
  have hsq_b_nonneg : 0 ≤ ∑ i : Fin n, (b i) ^ 2 := by
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (b i))
  have hsqrt_mul :
      √((∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (b i) ^ 2)) =
        √(∑ i : Fin n, (a i) ^ 2) * √(∑ i : Fin n, (b i) ^ 2) := by
    rw [Real.sqrt_mul hsq_a_nonneg]
  -- Reflect a around (2 / n) * (∑ a), i.e. around its own mean.  Reflecting
  -- preserves the sum of squared entries.
  have hreflect_sq :
      (∑ i : Fin n, (2 / (n : ℝ) * (∑ j : Fin n, a j) - a i) ^ 2) =
        ∑ i : Fin n, (a i) ^ 2 := by
    have hsum_expand :
        (∑ i : Fin n, (2 / (n : ℝ) * (∑ j : Fin n, a j) - a i) ^ 2) =
          (∑ i : Fin n, (a i) ^ 2) -
            2 * (2 / (n : ℝ) * (∑ j : Fin n, a j)) * (∑ i : Fin n, a i) +
              (n : ℝ) * (2 / (n : ℝ) * (∑ j : Fin n, a j)) ^ 2 := by
      let c : ℝ := 2 / (n : ℝ) * (∑ j : Fin n, a j)
      calc
        (∑ i : Fin n, (2 / (n : ℝ) * (∑ j : Fin n, a j) - a i) ^ 2) =
            ∑ i : Fin n, ((a i) ^ 2 - 2 * c * a i + c ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          dsimp [c]
          ring
        _ = (∑ i : Fin n, (a i) ^ 2) - 2 * c * (∑ i : Fin n, a i) +
              (n : ℝ) * c ^ 2 := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, Finset.sum_const, Fintype.card_fin]
        _ = (∑ i : Fin n, (a i) ^ 2) -
              2 * (2 / (n : ℝ) * (∑ j : Fin n, a j)) * (∑ i : Fin n, a i) +
                (n : ℝ) * (2 / (n : ℝ) * (∑ j : Fin n, a j)) ^ 2 := by
          dsimp [c]
    rw [hsum_expand]
    field_simp [hn_real_ne]
    ring
  -- The inner product of the reflected vector with b is
  -- (2 / n) * (∑ a) * (∑ b) - ∑ (a * b), by distributing the sum.
  have hreflect_dot :
      (∑ i : Fin n, (2 / (n : ℝ) * (∑ j : Fin n, a j) - a i) * b i) =
        2 / (n : ℝ) * (∑ i : Fin n, a i) * (∑ i : Fin n, b i) -
          ∑ i : Fin n, a i * b i := by
    simp [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  -- Cauchy--Schwarz bounds the reflected inner product by the split square
  -- roots; the previous identities make the right-hand side exactly the square
  -- root appearing in the statement.
  have hreflect_upper :
      (∑ i : Fin n, (2 / (n : ℝ) * (∑ j : Fin n, a j) - a i) * b i) ≤
        √((∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (b i) ^ 2)) := by
    have hcauchy :
        (∑ i : Fin n, (2 / (n : ℝ) * (∑ j : Fin n, a j) - a i) * b i) ≤
          √(∑ i : Fin n, (2 / (n : ℝ) * (∑ j : Fin n, a j) - a i) ^ 2) *
            √(∑ i : Fin n, (b i) ^ 2) := by
      simpa using
        (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n))
          (fun i => 2 / (n : ℝ) * (∑ j : Fin n, a j) - a i) b)
    rw [hreflect_sq] at hcauchy
    rw [hsqrt_mul]
    exact hcauchy
  -- Rewriting the Cauchy bound through the reflected inner product yields the
  -- target inequality with the dot-product term moved to the other side.
  have htarget_shifted :
      2 / (n : ℝ) * (∑ i : Fin n, a i) * (∑ i : Fin n, b i) -
          ∑ i : Fin n, a i * b i ≤
        √((∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (b i) ^ 2)) := by
    rwa [hreflect_dot] at hreflect_upper
  linarith
