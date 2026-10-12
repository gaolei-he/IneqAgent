import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

theorem simple :
    ∀ x : ℝ, x * (1 - x) ≤ 1 / 4 := by
  intro x
  have hsq_id : (x - 1 / 2) ^ 2 = 1 / 4 - x * (1 - x) := by
    ring
  have hsq_nonneg : 0 ≤ (x - 1 / 2) ^ 2 := by
    positivity
  nlinarith
