import Mathlib

theorem real_p35 (x y z : ℝ) (hx : x > -1) (hy : y > -1) (hz : z > -1) : (1 + x^2) / (1 + y + z^2) + (1 + y^2) / (1 + z + x^2) + (1 + z^2) / (1 + x + y^2) ≥ 2 := by
  have hD1 : 0 < 1 + y + z ^ 2 := by
    nlinarith [sq_nonneg z]
  have hD2 : 0 < 1 + z + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hD3 : 0 < 1 + x + y ^ 2 := by
    nlinarith [sq_nonneg y]
  have hA1 : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hA2 : 0 < 1 + y ^ 2 := by
    nlinarith [sq_nonneg y]
  have hA3 : 0 < 1 + z ^ 2 := by
    nlinarith [sq_nonneg z]
  let vA : Fin 3 → ℝ := ![1 + x ^ 2, 1 + y ^ 2, 1 + z ^ 2]
  let vD : Fin 3 → ℝ := ![1 + y + z ^ 2, 1 + z + x ^ 2, 1 + x + y ^ 2]
  let vG : Fin 3 → ℝ := fun i => vA i * vD i
  have hposD : ∀ i : Fin 3, 0 < vD i := by
    intro i
    fin_cases i <;> simp [vD, hD1, hD2, hD3]
  have hposA : ∀ i : Fin 3, 0 < vA i := by
    intro i
    fin_cases i <;> simp [vA, hA1, hA2, hA3]
  have hposG : ∀ i : Fin 3, 0 < vG i := by
    intro i
    exact mul_pos (hposA i) (hposD i)
  have h_cauchy :
      (∑ i : Fin 3, vA i) ^ 2 / (∑ i : Fin 3, vG i) ≤
        ∑ i : Fin 3, (vA i) ^ 2 / vG i := by
    simpa using
      (Finset.sq_sum_div_le_sum_sq_div (s := Finset.univ) (f := vA) (g := vG)
        (by intro i hi; exact hposG i))
  have hcancel : ∀ i : Fin 3, (vA i) ^ 2 / (vA i * vD i) = vA i / vD i := by
    intro i
    rw [sq]
    exact mul_div_mul_left (vA i) (vD i) (hposA i).ne'
  have h_engel_sums :
      (∑ i : Fin 3, vA i) ^ 2 / (∑ i : Fin 3, vA i * vD i) ≤
        ∑ i : Fin 3, vA i / vD i := by
    calc
      (∑ i : Fin 3, vA i) ^ 2 / (∑ i : Fin 3, vA i * vD i)
          ≤ ∑ i : Fin 3, (vA i) ^ 2 / (vA i * vD i) := by
            simpa [vG] using h_cauchy
      _ = ∑ i : Fin 3, vA i / vD i := by
          exact Finset.sum_congr rfl (by intro i hi; exact hcancel i)
  have hA_sum : (∑ i : Fin 3, vA i) = (1 + x ^ 2) + (1 + y ^ 2) + (1 + z ^ 2) := by
    rw [Fin.sum_univ_three]
    simp [vA]
  have hAD_sum :
      (∑ i : Fin 3, vA i * vD i) =
        (1 + x ^ 2) * (1 + y + z ^ 2) + (1 + y ^ 2) * (1 + z + x ^ 2) +
          (1 + z ^ 2) * (1 + x + y ^ 2) := by
    rw [Fin.sum_univ_three]
    simp [vA, vD]
  have hADiv_sum :
      (∑ i : Fin 3, vA i / vD i) =
        (1 + x ^ 2) / (1 + y + z ^ 2) + (1 + y ^ 2) / (1 + z + x ^ 2) +
          (1 + z ^ 2) / (1 + x + y ^ 2) := by
    rw [Fin.sum_univ_three]
    simp [vA, vD]
  have h_engel :
      ((1 + x ^ 2 + (1 + y ^ 2) + (1 + z ^ 2)) ^ 2 /
        ((1 + x ^ 2) * (1 + y + z ^ 2) + (1 + y ^ 2) * (1 + z + x ^ 2) +
          (1 + z ^ 2) * (1 + x + y ^ 2))) ≤
        (1 + x ^ 2) / (1 + y + z ^ 2) + (1 + y ^ 2) / (1 + z + x ^ 2) +
          (1 + z ^ 2) / (1 + x + y ^ 2) := by
    calc
      ((1 + x ^ 2 + (1 + y ^ 2) + (1 + z ^ 2)) ^ 2 /
          ((1 + x ^ 2) * (1 + y + z ^ 2) + (1 + y ^ 2) * (1 + z + x ^ 2) +
            (1 + z ^ 2) * (1 + x + y ^ 2)))
          = (∑ i : Fin 3, vA i) ^ 2 / (∑ i : Fin 3, vA i * vD i) := by
            rw [← hA_sum, ← hAD_sum]
      _ ≤ ∑ i : Fin 3, vA i / vD i := h_engel_sums
      _ = (1 + x ^ 2) / (1 + y + z ^ 2) + (1 + y ^ 2) / (1 + z + x ^ 2) +
          (1 + z ^ 2) / (1 + x + y ^ 2) := hADiv_sum
  have h_sumG_pos : 0 < (1 + x ^ 2) * (1 + y + z ^ 2) + (1 + y ^ 2) * (1 + z + x ^ 2) +
      (1 + z ^ 2) * (1 + x + y ^ 2) := by
    nlinarith [mul_pos hA1 hD1, mul_pos hA2 hD2, mul_pos hA3 hD3]
  have h_num :
      2 * ((1 + x ^ 2) * (1 + y + z ^ 2) + (1 + y ^ 2) * (1 + z + x ^ 2) +
          (1 + z ^ 2) * (1 + x + y ^ 2)) ≤
        (1 + x ^ 2 + (1 + y ^ 2) + (1 + z ^ 2)) ^ 2 := by
    have h1 : 0 ≤ (x ^ 2 - y) ^ 2 := sq_nonneg (x ^ 2 - y)
    have h2 : 0 ≤ (y ^ 2 - z) ^ 2 := sq_nonneg (y ^ 2 - z)
    have h3 : 0 ≤ (z ^ 2 - x) ^ 2 := sq_nonneg (z ^ 2 - x)
    have h4 : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
    have h5 : 0 ≤ (y - 1) ^ 2 := sq_nonneg (y - 1)
    have h6 : 0 ≤ (z - 1) ^ 2 := sq_nonneg (z - 1)
    nlinarith
  have hq : 2 ≤
      (1 + x ^ 2 + (1 + y ^ 2) + (1 + z ^ 2)) ^ 2 /
        ((1 + x ^ 2) * (1 + y + z ^ 2) + (1 + y ^ 2) * (1 + z + x ^ 2) +
          (1 + z ^ 2) * (1 + x + y ^ 2)) := by
    rw [le_div_iff₀ h_sumG_pos]
    nlinarith
  exact hq.trans h_engel
