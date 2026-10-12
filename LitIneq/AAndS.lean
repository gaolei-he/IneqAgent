import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

def G (x : ℝ) : ℝ :=
  3 * x / 2 - Real.log (1 - x)

theorem A_and_S :
    G 0.5828 > 0 := by
  unfold G
  -- y := 1 - x is positive, so log y ≤ y - 1.
  have hy : (0 : ℝ) < 1 - (0.5828 : ℝ) := by
    norm_num
  have hlog_le :
      Real.log (1 - (0.5828 : ℝ)) ≤ (1 - (0.5828 : ℝ)) - 1 := by
    simpa using Real.log_le_sub_one_of_pos hy
  -- Negating hlog_le gives -log (1-x) ≥ x, hence G x ≥ 3*x/2 + x.
  have hG_lower :
      3 * (0.5828 : ℝ) / 2 - Real.log (1 - (0.5828 : ℝ)) ≥
        3 * (0.5828 : ℝ) / 2 + (0.5828 : ℝ) := by
    linarith
  have hpos : (0 : ℝ) < 3 * (0.5828 : ℝ) / 2 + (0.5828 : ℝ) := by
    norm_num
  linarith
