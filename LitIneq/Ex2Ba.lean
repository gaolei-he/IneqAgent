import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

theorem ex2_ba :
    ∀ x : ℝ, 0 ≤ x ∧ x ≤ 0.9 →
      Real.log (1 - x) - 0.1 ≤ -x := by
  intro x hx
  rcases hx with ⟨hx0, hx09⟩
  have hx_lt_one : x < 1 := by nlinarith
  have hpos : 0 < 1 - x := by linarith
  have hlog_tangent : Real.log (1 - x) ≤ -x := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlog_shifted : Real.log (1 - x) - 0.1 ≤ -x := by
    linarith
  exact hlog_shifted
