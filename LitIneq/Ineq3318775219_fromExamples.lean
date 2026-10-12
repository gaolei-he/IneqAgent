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

def dihY (y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  let x1 := y1 * y1
  let x2 := y2 * y2
  let x3 := y3 * y3
  let x4 := y4 * y4
  let x5 := y5 * y5
  let x6 := y6 * y6
  dihX x1 x2 x3 x4 x5 x6

theorem ineq3318775219_fromExamples :
    ∀ y1 y2 y3 y4 y5 y6 : ℝ,
      2 ≤ y1 ∧ y1 ≤ 2.52 ∧
      2 ≤ y2 ∧ y2 ≤ 2.52 ∧
      2 ≤ y3 ∧ y3 ≤ 2.52 ∧
      2.52 ≤ y4 ∧ y4 ≤ Real.sqrt 8 ∧
      2 ≤ y5 ∧ y5 ≤ 2.52 ∧
      2 ≤ y6 ∧ y6 ≤ 2.52 →
        (dihY y1 y2 y3 y4 y5 y6 - 1.629
          + 0.414 * (y2 + y3 + y5 + y6 - 8.0)
          - 0.763 * (y4 - 2.52)
          - 0.315 * (y1 - 2.0)) * (-1) < 0 := by
  sorry

end
