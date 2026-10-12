import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

theorem ex3_ba :
    ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 / 2 →
      -x - 2 * (x * x) - 0.1 ≤ Real.log (1 - x) := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have hxden : 0 < 1 - x := by linarith
  have hlog : 1 - (1 - x)⁻¹ ≤ Real.log (1 - x) :=
    Real.one_sub_inv_le_log_of_pos hxden
  have halg : -x - 2 * (x * x) - (0.1 : ℝ) ≤ -x / (1 - x) := by
    rw [le_div_iff₀ hxden]
    have hq1 : 0 ≤ (1 - x) * (1 / 10 : ℝ) := by positivity
    have hq2 : 0 ≤ (x * x) * (1 - 2 * x) := by
      exact mul_nonneg (mul_self_nonneg x) (by linarith)
    have hq : 0 ≤ (1 - x) * (1 / 10 : ℝ) + (x * x) * (1 - 2 * x) := by
      exact add_nonneg hq1 hq2
    nlinarith [hq]
  have hfrac : 1 - (1 - x)⁻¹ = -x / (1 - x) := by
    field_simp [hxden.ne']
    ring
  have hlog' : -x / (1 - x) ≤ Real.log (1 - x) := by
    simpa [hfrac] using hlog
  exact halg.trans hlog'
