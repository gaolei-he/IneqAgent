import Mathlib

private lemma term_lower_bound (x : ℝ) (hx : x > 0) (hx2 : x ^ 2 < 1) :
    x / (1 - x ^ 2) ≥ (3 * √3 / 2) * x ^ 2 := by
  have hda : 0 < 1 - x ^ 2 := by linarith
  have hsqrt : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h4x : 0 < 4 - 3 * x ^ 2 := by nlinarith
  have hfac : 4 - 27 * x ^ 2 * (1 - x ^ 2)^2 = (1 - 3*x ^ 2)^2 * (4 - 3 * x ^ 2) := by ring
  have hcube : 27 * x ^ 2 * (1 - x ^ 2)^2 ≤ 4 := by
    have hle : 0 ≤ 4 - 27 * x ^ 2 * (1 - x ^ 2)^2 := by
      rw [hfac]
      positivity
    linarith
  have hRnonneg : 0 ≤ (3 * √3 / 2) * (x * (1 - x ^ 2)) := by
    positivity
  have hRsq : ((3 * √3 / 2) * (x * (1 - x ^ 2)))^2 ≤ 1 := by
    nlinarith [hcube, hsqrt]
  have hRle : (3 * √3 / 2) * (x * (1 - x ^ 2)) ≤ 1 := by
    have hAbs : |(3 * √3 / 2) * (x * (1 - x ^ 2))| ≤ |(1 : ℝ)| :=
      (sq_le_sq.mp (by simpa using hRsq))
    rw [abs_of_nonneg hRnonneg] at hAbs
    norm_num at hAbs
    linarith
  have hmult : (3 * √3 / 2) * x ^ 2 * (1 - x ^ 2) ≤ x := by nlinarith [hRle]
  exact (le_div_iff₀ hda).2 hmult

theorem real_p25 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a^2 + b^2 + c^2 = 1) : a / (1 - a^2) + b / (1 - b^2) + c / (1 - c^2) ≥ 3 * √3 / 2 := by
  have hb2 : (0 : ℝ) < b ^ 2 := sq_pos_of_ne_zero (ne_of_gt hb)
  have hc2 : (0 : ℝ) < c ^ 2 := sq_pos_of_ne_zero (ne_of_gt hc)
  have ha2lt : a ^ 2 < 1 := by nlinarith [h, hb2, hc2]
  have ha2 : (0 : ℝ) < a ^ 2 := sq_pos_of_ne_zero (ne_of_gt ha)
  have hb2lt : b ^ 2 < 1 := by nlinarith [h, ha2, hc2]
  have hc2lt : c ^ 2 < 1 := by nlinarith [h, ha2, hb2]
  have ha_term : a / (1 - a^2) ≥ (3 * √3 / 2) * a^2 := term_lower_bound a ha ha2lt
  have hb_term : b / (1 - b^2) ≥ (3 * √3 / 2) * b^2 := term_lower_bound b hb hb2lt
  have hc_term : c / (1 - c^2) ≥ (3 * √3 / 2) * c^2 := term_lower_bound c hc hc2lt
  have hsum1 : a / (1 - a^2) + b / (1 - b^2) + c / (1 - c^2) ≥ (3 * √3 / 2) * (a^2 + b^2 + c^2) := by
    nlinarith [ha_term, hb_term, hc_term]
  have hsum2 : (3 * √3 / 2) * (a^2 + b^2 + c^2) = 3 * √3 / 2 := by
    calc
      (3 * √3 / 2) * (a^2 + b^2 + c^2) = (3 * √3 / 2) * 1 := by rw [h]
      _ = 3 * √3 / 2 := by ring
  nlinarith
