import Mathlib

theorem real_p36 (n : ℕ) (hn : n ≥ 2) (a : Fin n → ℝ) (ha : ∀ i, a i > 0) (h : ∑ i : Fin n, a i = 1) : ∑ i : Fin n, (a i / (2 - a i)) ≥ n / (2 * n - 1) := by
  have ha_le_one : ∀ i : Fin n, a i ≤ 1 := by
    intro i
    have hle : a i ≤ ∑ x : Fin n, a x := by
      simpa using (Finset.single_le_sum (s := Finset.univ) (f := a)
        (fun j hj => le_of_lt (ha j)) (Finset.mem_univ i))
    linarith [hle, h]
  have h2a_pos : ∀ i : Fin n, 0 < 2 - a i := by
    intro i
    linarith [ha_le_one i]
  have hg_pos : ∀ i : Fin n, 0 < a i * (2 - a i) := by
    intro i
    exact mul_pos (ha i) (h2a_pos i)
  set S : ℝ := ∑ i : Fin n, a i ^ 2 with hS
  have hD : (∑ i : Fin n, a i * (2 - a i)) = 2 - S := by
    rw [hS]
    have hrew : (∑ i : Fin n, a i * (2 - a i)) =
        (∑ i : Fin n, (2 * a i - a i ^ 2)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hrew, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    rw [h]
    ring
  have hS_le_one : S ≤ 1 := by
    have hmul : ∀ i : Fin n, a i ^ 2 ≤ a i := by
      intro i
      nlinarith [mul_nonneg (le_of_lt (ha i)) (sub_nonneg.mpr (ha_le_one i))]
    rw [hS]
    calc
      (∑ i : Fin n, a i ^ 2) ≤ ∑ i : Fin n, a i := Finset.sum_le_sum (fun i hi => hmul i)
      _ = 1 := h
  have hDpos : 0 < ∑ i : Fin n, a i * (2 - a i) := by
    rw [hD]
    linarith
  have hge2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2n1_pos : 0 < 2 * (n : ℝ) - 1 := by
    linarith
  have hS_ge_inv : 1 ≤ (n : ℝ) * S := by
    have hc : (∑ i : Fin n, a i) ^ 2 ≤ (n : ℝ) * (∑ i : Fin n, a i ^ 2) := by
      simpa using (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => a i))
    rw [h, one_pow] at hc
    simpa [hS] using hc
  have htitu : 1 / (∑ i : Fin n, a i * (2 - a i)) ≤
      ∑ i : Fin n, a i / (2 - a i) := by
    have ht0 : (∑ i : Fin n, a i) ^ 2 / (∑ i : Fin n, a i * (2 - a i)) ≤
        ∑ i : Fin n, a i ^ 2 / (a i * (2 - a i)) := by
      simpa using (Finset.sq_sum_div_le_sum_sq_div (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => a i) (g := fun i : Fin n => a i * (2 - a i))
        (fun j hj => hg_pos j))
    rw [h, one_pow] at ht0
    have hterm : (∑ i : Fin n, a i ^ 2 / (a i * (2 - a i))) =
        (∑ i : Fin n, a i / (2 - a i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h0 : a i ≠ 0 := ne_of_gt (ha i)
      have hd : 2 - a i ≠ 0 := by linarith [ha_le_one i]
      field_simp [h0, hd]
    rwa [hterm] at ht0
  have hnum_ineq : (n : ℝ) / (2 * (n : ℝ) - 1) ≤ 1 / (∑ i : Fin n, a i * (2 - a i)) := by
    rw [le_div_iff₀ hDpos]
    rw [hD]
    have hmul : (n : ℝ) / (2 * (n : ℝ) - 1) * (2 - S) =
        (n : ℝ) * (2 - S) / (2 * (n : ℝ) - 1) := by ring
    rw [hmul, div_le_iff₀ h2n1_pos]
    nlinarith [hS_ge_inv]
  calc
    n / (2 * n - 1) ≤ 1 / (∑ i : Fin n, a i * (2 - a i)) := hnum_ineq
    _ ≤ ∑ i : Fin n, a i / (2 - a i) := htitu
