import Mathlib

theorem real_p33 (n : ℕ) (k : ℝ) (a : Fin n → ℝ) (hn : n > 0) (hk : k > 0) (ha : ∀ i, a i > 0) (h : ∑ i : Fin n, a i = k) : ∑ i : Fin n, (a i + 1 / a i)^2 ≥ n * ((n^2 + k^2) / (n * k))^2 := by
  classical
  have hn_real_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hn_real_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_real_pos
  have hk_nonneg : 0 ≤ k := le_of_lt hk
  have hk_ne : k ≠ 0 := ne_of_gt hk
  have ha_nonneg : ∀ i : Fin n, 0 ≤ a i := fun i => le_of_lt (ha i)
  have ha_ne : ∀ i : Fin n, a i ≠ 0 := fun i => ne_of_gt (ha i)
  have hsum_inv_lower : (n : ℝ) ^ 2 / k ≤ ∑ i : Fin n, 1 / a i := by
    have hsed :=
      Finset.sq_sum_div_le_sum_sq_div (s := Finset.univ) (f := fun _ : Fin n => (1 : ℝ))
        (g := fun i : Fin n => a i) (by
          intro i _
          exact ha i)
    simpa [h, Finset.card_univ, Fintype.card_fin] using hsed
  have hsum_linear_lower :
      (n : ℝ) ^ 2 / k + k ≤ ∑ i : Fin n, (a i + 1 / a i) := by
    calc
      (n : ℝ) ^ 2 / k + k ≤ (∑ i : Fin n, 1 / a i) + (∑ i : Fin n, a i) := by
        exact add_le_add hsum_inv_lower (by rw [h])
      _ = ∑ i : Fin n, (a i + 1 / a i) := by
        rw [Finset.sum_add_distrib, add_comm]
  have hsum_linear_nonneg : 0 ≤ ∑ i : Fin n, (a i + 1 / a i) := by
    exact Finset.sum_nonneg fun i _ =>
      add_nonneg (ha_nonneg i) (one_div_nonneg.mpr (ha_nonneg i))
  have hsum_sq_cauchy :
      (∑ i : Fin n, (a i + 1 / a i)) ^ 2 ≤
        (n : ℝ) * ∑ i : Fin n, (a i + 1 / a i) ^ 2 := by
    have hcheb :=
      sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin n => a i + 1 / a i)
    simpa [Finset.card_univ, Fintype.card_fin] using hcheb
  have hsum_sq_lower :
      (∑ i : Fin n, (a i + 1 / a i)) ^ 2 / (n : ℝ) ≤
        ∑ i : Fin n, (a i + 1 / a i) ^ 2 := by
    rw [div_le_iff₀ hn_real_pos]
    simpa [mul_comm] using hsum_sq_cauchy
  have hlinear_fraction :
      (n : ℝ) ^ 2 / k + k = ((n : ℝ) ^ 2 + k ^ 2) / k := by
    field_simp [hk_ne]
  have hlinear_fraction_nonneg : 0 ≤ ((n : ℝ) ^ 2 + k ^ 2) / k := by
    rw [← hlinear_fraction]
    exact add_nonneg (div_nonneg (sq_nonneg _) hk_nonneg) hk_nonneg
  have hlinear_fraction_lower :
      ((n : ℝ) ^ 2 + k ^ 2) / k ≤ ∑ i : Fin n, (a i + 1 / a i) := by
    rwa [← hlinear_fraction]
  have hlinear_sq_lower :
      (((n : ℝ) ^ 2 + k ^ 2) / k) ^ 2 ≤
        (∑ i : Fin n, (a i + 1 / a i)) ^ 2 := by
    exact (sq_le_sq₀ hlinear_fraction_nonneg hsum_linear_nonneg).2 hlinear_fraction_lower
  have hmain_lower :
      (((n : ℝ) ^ 2 + k ^ 2) / k) ^ 2 / (n : ℝ) ≤
        ∑ i : Fin n, (a i + 1 / a i) ^ 2 := by
    calc
      (((n : ℝ) ^ 2 + k ^ 2) / k) ^ 2 / (n : ℝ) ≤
          (∑ i : Fin n, (a i + 1 / a i)) ^ 2 / (n : ℝ) := by
        exact div_le_div_of_nonneg_right hlinear_sq_lower hn_real_nonneg
      _ ≤ ∑ i : Fin n, (a i + 1 / a i) ^ 2 := hsum_sq_lower
  calc
    ∑ i : Fin n, (a i + 1 / a i) ^ 2 ≥
        (((n : ℝ) ^ 2 + k ^ 2) / k) ^ 2 / (n : ℝ) := hmain_lower
    _ = (n : ℝ) * (((n : ℝ) ^ 2 + k ^ 2) / ((n : ℝ) * k)) ^ 2 := by
      field_simp [hk_ne, ne_of_gt hn_real_pos]
