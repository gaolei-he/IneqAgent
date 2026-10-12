import Mathlib

set_option linter.style.header false
set_option linter.unusedVariables false

noncomputable section

def atn2 (x y : ℝ) : ℝ :=
  Real.arctan (y / x)

def upsX (x1 x2 x6 : ℝ) : ℝ :=
  -x1 * x1 - x2 * x2 - x6 * x6
  + 2 * x1 * x6 + 2 * x1 * x2 + 2 * x2 * x6

def arclength (a b c : ℝ) : ℝ :=
  Real.pi / 2 + atn2 (Real.sqrt (upsX (a * a) (b * b) (c * c))) (c * c - a * a - b * b)

def arclengthY1 (a b y1 y2 y3 y4 y5 y6 : ℝ) : ℝ :=
  arclength y1 a b

def arclengthX1 (a b x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  arclengthY1 a b (Real.sqrt x1) (Real.sqrt x2) (Real.sqrt x3)
    (Real.sqrt x4) (Real.sqrt x5) (Real.sqrt x6)

theorem ineqSDCCMGA_b :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      4.0 ≤ x1 ∧ x1 ≤ 6.3504 ∧
      1 * 1 ≤ x2 ∧ x2 ≤ 1 * 1 ∧
      1 * 1 ≤ x3 ∧ x3 ≤ 1 * 1 ∧
      1 * 1 ≤ x4 ∧ x4 ≤ 1 * 1 ∧
      1 * 1 ≤ x5 ∧ x5 ≤ 1 * 1 ∧
      1 * 1 ≤ x6 ∧ x6 ≤ 1 * 1 →
        arclengthX1 2.0 (2.0 * 1.26) x1 x2 x3 x4 x5 x6
        + arclengthX1 2.0 (2.0 * 1.26) x1 x2 x3 x4 x5 x6
        + arclengthX1 (2.0 * 1.26) 2.0 x1 x2 x3 x4 x5 x6 * (-1)
        + Real.pi * (-(1 / 3))
        + (-(arclength (2 * 1.26) (2 * 1.26) 2)) < 0 := by
  sorry

end
