import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

theorem ex7_ba :
    ∀ x : ℝ, 0 ≤ x ∧ x ≤ 1 →
      Real.exp (x - x ^ 2) - 0.1 ≤ 1 + x := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  let t : ℝ := x - x ^ 2
  have ht0 : 0 ≤ t := by
    dsimp [t]
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
  have ht1 : t ≤ 1 := by
    dsimp [t]
    nlinarith [sq_nonneg x]
  have habs_abs : |t| ≤ 1 := by
    rw [abs_of_nonneg ht0]
    exact ht1
  have hexp_le : Real.exp t ≤ 1 + t + t ^ 2 := by
    have hb := Real.abs_exp_sub_one_sub_id_le habs_abs
    have hres : Real.exp t - 1 - t ≤ t ^ 2 := by
      simpa using (abs_le.mp hb).2
    linarith
  have hpoly : x ^ 4 - 2 * x ^ 3 ≤ 0.1 := by
    have hprod : x ^ 3 * (x - 2) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    nlinarith
  have hexp_upper : Real.exp t ≤ 1 + x + 0.1 := by
    calc
      Real.exp t ≤ 1 + t + t ^ 2 := hexp_le
      _ ≤ 1 + x + 0.1 := by
        dsimp [t]
        nlinarith [hpoly]
  linarith
