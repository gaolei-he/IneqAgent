import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

theorem ex6_ba :
    ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 →
      Real.exp x - 0.1 ≤ 1 + x + x * x := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have h_exp_taylor := Real.exp_bound' hx0 hx1 (n := 2) (by norm_num)
  have h_exp_quad : Real.exp x ≤ 1 + x + x * x := by
    norm_num [Finset.sum_range_succ, pow_two] at h_exp_taylor
    nlinarith [sq_nonneg x]
  nlinarith
