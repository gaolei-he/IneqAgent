import Mathlib

set_option linter.style.header false

noncomputable section

def atn2 (x y : ℝ) : ℝ :=
  Real.arctan (y / x)

def deltaX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6)
  + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6)
  + x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6)
  - x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6

def deltaX4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6
  + x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

def dihX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let dX4 := deltaX4 x1 x2 x3 x4 x5 x6
  let d := deltaX x1 x2 x3 x4 x5 x6
  Real.pi / 2 + atn2 (Real.sqrt (4 * x1 * d)) (-dX4)

theorem ineq7067938795 :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      4.0 ≤ x1 ∧ x1 ≤ 6.3504 ∧
      4.0 ≤ x2 ∧ x2 ≤ 6.3504 ∧
      4.0 ≤ x3 ∧ x3 ≤ 6.3504 ∧
      4.0 ≤ x4 ∧ x4 ≤ 4.0 ∧
      3.01 * 3.01 ≤ x5 ∧ x5 ≤ 3.24 * 3.24 ∧
      3.01 * 3.01 ≤ x6 ∧ x6 ≤ 3.24 * 3.24 →
        dihX x1 x2 x3 x4 x5 x6
        + Real.pi * (-(1 / 2.0))
        + 0.46 < 0 := by
  sorry

end
