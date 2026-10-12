import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

theorem ex1_ba :
    ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 →
      x - x ^ 2 - 0.1 ≤ Real.log (1 + x) := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have hx2 : 0 < x + 2 := by nlinarith
  -- Lower bound `2 * x / (x + 2) ≤ log (1 + x)` for every nonnegative `x`.
  have hlog : 2 * x / (x + 2) ≤ Real.log (1 + x) :=
    Real.le_log_one_add_of_nonneg hx0
  -- Reduce the target to the algebraic bound above.
  have halg : x - x ^ 2 - 0.1 ≤ 2 * x / (x + 2) := by
    rw [le_div_iff₀ hx2]
    have hx2sq : 0 ≤ x ^ 2 := sq_nonneg x
    have hx3sq : 0 ≤ x ^ 3 := by
      nlinarith [mul_nonneg hx2sq hx0]
    nlinarith
  exact le_trans halg hlog
