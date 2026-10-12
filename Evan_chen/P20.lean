import Mathlib

private lemma cauchy_engel_three (a b c : ℝ) :
    (a + b + c - 3) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2 + 3) ≤
      (a - 1) ^ 2 / (a ^ 2 + 1) + (b - 1) ^ 2 / (b ^ 2 + 1) +
        (c - 1) ^ 2 / (c ^ 2 + 1) := by
  let u : Fin 3 → ℝ := ![a - 1, b - 1, c - 1]
  let v : Fin 3 → ℝ := ![a ^ 2 + 1, b ^ 2 + 1, c ^ 2 + 1]
  have hv : ∀ i : Fin 3, 0 < v i := by
    intro i
    fin_cases i <;> simp [v] <;> positivity
  have h := Finset.sq_sum_div_le_sum_sq_div (R := ℝ) Finset.univ u (g := v)
    (fun i _hi => hv i)
  have hsum : (∑ i : Fin 3, u i) = a + b + c - 3 := by
    simp [u, Fin.sum_univ_three]
    ring
  have hden : (∑ i : Fin 3, v i) = a ^ 2 + b ^ 2 + c ^ 2 + 3 := by
    simp [v, Fin.sum_univ_three]
    ring
  have hrhs : (∑ i : Fin 3, u i ^ 2 / v i) =
      (a - 1) ^ 2 / (a ^ 2 + 1) + (b - 1) ^ 2 / (b ^ 2 + 1) +
        (c - 1) ^ 2 / (c ^ 2 + 1) := by
    simp [u, v, Fin.sum_univ_three]
  calc
    (a - 1) ^ 2 / (a ^ 2 + 1) + (b - 1) ^ 2 / (b ^ 2 + 1) +
        (c - 1) ^ 2 / (c ^ 2 + 1)
        = ∑ i : Fin 3, u i ^ 2 / v i := hrhs.symm
    _ ≥ (∑ i : Fin 3, u i) ^ 2 / ∑ i : Fin 3, v i := by simpa [hsum, hden] using h
    _ = (a + b + c - 3) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2 + 3) := by rw [hsum, hden]

theorem P20 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : 2 * (a + b + c) ≤ (a * b + b * c + c * a)) : 3 / 5 ≤ (a - 1) ^ 2 / (a ^ 2 + 1) + (b - 1) ^ 2 / (b ^ 2 + 1) + (c - 1) ^ 2 / (c ^ 2 + 1) := by
  let p : ℝ := a + b + c
  let s : ℝ := a ^ 2 + b ^ 2 + c ^ 2
  have hp_pos : 0 < p := by
    dsimp [p]
    nlinarith
  have hpq : p ^ 2 - 3 * (a * b + b * c + c * a) ≥ 0 := by
    dsimp [p]
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hpmul : 0 ≤ p * (p - 6) := by
    dsimp [p]
    nlinarith
  have hp_ge : 6 ≤ p := by
    have : 0 ≤ p - 6 := nonneg_of_mul_nonneg_right hpmul hp_pos
    linarith
  have hs_le : s ≤ p ^ 2 - 4 * p := by
    dsimp [p, s]
    nlinarith
  have hden_pos : 0 < s + 3 := by
    dsimp [s]
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  have hnum : 3 * (s + 3) ≤ 5 * (p - 3) ^ 2 := by
    nlinarith
  have hfrac : 3 / 5 ≤ (p - 3) ^ 2 / (s + 3) := by
    rw [le_div_iff₀ hden_pos]
    nlinarith
  have hcauchy : (p - 3) ^ 2 / (s + 3) ≤
      (a - 1) ^ 2 / (a ^ 2 + 1) + (b - 1) ^ 2 / (b ^ 2 + 1) +
        (c - 1) ^ 2 / (c ^ 2 + 1) := by
    simpa [p, s] using cauchy_engel_three a b c
  exact le_trans hfrac hcauchy
