import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

/-- On `u ∈ [0, 1/2]`, the first-order Taylor remainder of `log (1 - u)` is at
most `2 * u ^ 2` in absolute value. -/
private lemma ex5_ba_log_bound_aux (u : ℝ) (hu0 : 0 ≤ u) (hu2 : u ≤ 1 / 2) :
    |Real.log (1 - u) + u| ≤ 2 * u ^ 2 := by
  have hu_abs : |u| < (1 : ℝ) := by
    rw [abs_of_nonneg hu0]
    linarith
  have hsum := Real.abs_log_sub_add_sum_range_le hu_abs 1
  have hden : 0 < 1 - u := by linarith
  have hquad : 0 ≤ u ^ 2 * (1 - 2 * u) := by
    exact mul_nonneg (sq_nonneg u) (by linarith)
  have hb : u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hsum' : |Real.log (1 - u) + u| ≤ u ^ 2 / (1 - u) := by
    simpa [abs_of_nonneg hu0, add_comm] using hsum
  exact hsum'.trans hb

theorem ex5_ba :
    ∀ x : ℝ, -1 / 2 ≤ x ∧ x ≤ 0 →
      |Real.log (1 + x) - x| - 0.1 ≤ 2 * (x * x) := by
  intro x hx
  rcases hx with ⟨hxm, hx0⟩
  have hu0 : 0 ≤ -x := by linarith
  have hu2 : -x ≤ 1 / 2 := by linarith
  have hbound := ex5_ba_log_bound_aux (-x) hu0 hu2
  have hmain : |Real.log (1 + x) - x| ≤ 2 * (x * x) := by
    simpa [sub_eq_add_neg, neg_neg, add_comm, mul_comm, pow_two] using hbound
  nlinarith [hmain]
