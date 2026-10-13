import Mathlib

set_option linter.style.header false


set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

private theorem ineq6096597438a_real_value :
    (0.591 : ℝ)
        + 0.0331 * (-64)
        + 0.506 * 1.26 * 1 / (1.26 + (-1))
        + 0.506 * (-(1 / (1.26 + (-1))))
        + 1.0 < 0 := by
  norm_num

theorem ineq6096597438a :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      1.0 ≤ x1 ∧ x1 ≤ 1.0 ∧
      1 ≤ x2 ∧ x2 ≤ 1 ∧
      1 ≤ x3 ∧ x3 ≤ 1 ∧
      1 ≤ x4 ∧ x4 ≤ 1 ∧
      1 ≤ x5 ∧ x5 ≤ 1 ∧
      1 ≤ x6 ∧ x6 ≤ 1 →
        0.591
        + 0.0331 * (-64)
        + 0.506 * 1.26 * 1 / (1.26 + (-1))
        + 0.506 * (-(1 / (1.26 + (-1))))
        + 1.0 < 0 := by
  intro x1 x2 x3 x4 x5 x6 _
  native_decide
