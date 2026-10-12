import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert
import Mathlib.Tactic.IntervalCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace Lean92.BoxPoly45_BoxPoly45_14

theorem result (x1 x2 x3 x4 x5 x6 x7 : ℝ) (hl0 : (-1 : ℝ) ≤ x1) (hu0 : x1 ≤ (1 : ℝ)) (hl1 : (-1 : ℝ) ≤ x2) (hu1 : x2 ≤ (1 : ℝ)) (hl2 : (-1 : ℝ) ≤ x3) (hu2 : x3 ≤ (1 : ℝ)) (hl3 : (-1 : ℝ) ≤ x4) (hu3 : x4 ≤ (1 : ℝ)) (hl4 : (-1 : ℝ) ≤ x5) (hu4 : x5 ≤ (1 : ℝ)) (hl5 : (-1 : ℝ) ≤ x6) (hu5 : x6 ≤ (1 : ℝ)) (hl6 : (-1 : ℝ) ≤ x7) (hu6 : x7 ≤ (1 : ℝ)) : (0 : ℝ) ≤ x1^2 - x1 + 2*x2^2 + 2*x3^2 + 2*x4^2 + 2*x5^2 + 2*x6^2 + 2*x7^2 + 25001/100000 := by
  have hcert : (0 : ℝ) ≤ ((x1)^2) + ((-1)*(x1)) + ((2)*((x2)^2)) + ((2)*((x3)^2)) + ((2)*((x4)^2)) + ((2)*((x5)^2)) + ((2)*((x6)^2)) + ((2)*((x7)^2)) + (25001/100000) := by
    have hgg1 : (0 : ℝ) ≤ (x1) + (1) := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ 0 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg10 : (0 : ℝ) ≤ (1) + ((-1)*(x5)) := by first | positivity | nlinarith
    have hsg10 : (0 : ℝ) ≤ 0 := by positivity
    have hpg10 := mul_nonneg hsg10 hgg10
    have hgg11 : (0 : ℝ) ≤ (x6) + (1) := by first | positivity | nlinarith
    have hsg11 : (0 : ℝ) ≤ 0 := by positivity
    have hpg11 := mul_nonneg hsg11 hgg11
    have hgg12 : (0 : ℝ) ≤ (1) + ((-1)*(x6)) := by first | positivity | nlinarith
    have hsg12 : (0 : ℝ) ≤ 0 := by positivity
    have hpg12 := mul_nonneg hsg12 hgg12
    have hgg13 : (0 : ℝ) ≤ (x7) + (1) := by first | positivity | nlinarith
    have hsg13 : (0 : ℝ) ≤ 0 := by positivity
    have hpg13 := mul_nonneg hsg13 hgg13
    have hgg14 : (0 : ℝ) ≤ (1) + ((-1)*(x7)) := by first | positivity | nlinarith
    have hsg14 : (0 : ℝ) ≤ 0 := by positivity
    have hpg14 := mul_nonneg hsg14 hgg14
    have hgg2 : (0 : ℝ) ≤ (1) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ 0 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hgg3 : (0 : ℝ) ≤ (x2) + (1) := by first | positivity | nlinarith
    have hsg3 : (0 : ℝ) ≤ 0 := by positivity
    have hpg3 := mul_nonneg hsg3 hgg3
    have hgg4 : (0 : ℝ) ≤ (1) + ((-1)*(x2)) := by first | positivity | nlinarith
    have hsg4 : (0 : ℝ) ≤ 0 := by positivity
    have hpg4 := mul_nonneg hsg4 hgg4
    have hgg5 : (0 : ℝ) ≤ (x3) + (1) := by first | positivity | nlinarith
    have hsg5 : (0 : ℝ) ≤ 0 := by positivity
    have hpg5 := mul_nonneg hsg5 hgg5
    have hgg6 : (0 : ℝ) ≤ (1) + ((-1)*(x3)) := by first | positivity | nlinarith
    have hsg6 : (0 : ℝ) ≤ 0 := by positivity
    have hpg6 := mul_nonneg hsg6 hgg6
    have hgg7 : (0 : ℝ) ≤ (x4) + (1) := by first | positivity | nlinarith
    have hsg7 : (0 : ℝ) ≤ 0 := by positivity
    have hpg7 := mul_nonneg hsg7 hgg7
    have hgg8 : (0 : ℝ) ≤ (1) + ((-1)*(x4)) := by first | positivity | nlinarith
    have hsg8 : (0 : ℝ) ≤ 0 := by positivity
    have hpg8 := mul_nonneg hsg8 hgg8
    have hgg9 : (0 : ℝ) ≤ (x5) + (1) := by first | positivity | nlinarith
    have hsg9 : (0 : ℝ) ≤ 0 := by positivity
    have hpg9 := mul_nonneg hsg9 hgg9
    have hs0 : (0 : ℝ) ≤ (100000/25001)*((25001/100000) - (1/2)*x1)^2 + (1/2)*((2/1)*x7)^2 + (1/2)*((2/1)*x6)^2 + (1/2)*((2/1)*x5)^2 + (1/2)*((2/1)*x4)^2 + (1/2)*((2/1)*x3)^2 + (1/2)*((2/1)*x2)^2 + (25001/1)*((1/25001)*x1)^2 := by positivity
    have hid : (((x1)^2) + ((-1)*(x1)) + ((2)*((x2)^2)) + ((2)*((x3)^2)) + ((2)*((x4)^2)) + ((2)*((x5)^2)) + ((2)*((x6)^2)) + ((2)*((x7)^2)) + (25001/100000)) = (((100000/25001)*((25001/100000) - (1/2)*x1)^2 + (1/2)*((2/1)*x7)^2 + (1/2)*((2/1)*x6)^2 + (1/2)*((2/1)*x5)^2 + (1/2)*((2/1)*x4)^2 + (1/2)*((2/1)*x3)^2 + (1/2)*((2/1)*x2)^2 + (25001/1)*((1/25001)*x1)^2) + (0)*((x1) + (1)) + (0)*((1) + ((-1)*(x1))) + (0)*((x2) + (1)) + (0)*((1) + ((-1)*(x2))) + (0)*((x3) + (1)) + (0)*((1) + ((-1)*(x3))) + (0)*((x4) + (1)) + (0)*((1) + ((-1)*(x4))) + (0)*((x5) + (1)) + (0)*((1) + ((-1)*(x5))) + (0)*((x6) + (1)) + (0)*((1) + ((-1)*(x6))) + (0)*((x7) + (1)) + (0)*((1) + ((-1)*(x7)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring

end Lean92.BoxPoly45_BoxPoly45_14


set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 14
name: 7-Variable Magnetism
source_status: confirmed_transformed
basis: 679
paper_title: Formalization of Bernstein Polynomials and Applications to Global Optimization / A Tool for Formal Verification of Nonlinear Inequalities
paper_url: https://doi.org/10.1007/s10817-012-9256-3
source_evidence: paper_examples_extract/bernstein.txt:2340-2342,2352; paper_examples_extract/FormalVerifier.txt:325

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_14_7_variable_magnetism :
    ∀ x1 x2 x3 x4 x5 x6 x7 : ℝ,
      -1 <= x1 ∧
      x1 <= 1 ∧
      -1 <= x2 ∧
      x2 <= 1 ∧
      -1 <= x3 ∧
      x3 <= 1 ∧
      -1 <= x4 ∧
      x4 <= 1 ∧
      -1 <= x5 ∧
      x5 <= 1 ∧
      -1 <= x6 ∧
      x6 <= 1 ∧
      -1 <= x7 ∧
      x7 <= 1 →
        0 <= x1^2 - x1 + 2*x2^2 + 2*x3^2 + 2*x4^2 + 2*x5^2 + 2*x6^2 + 2*x7^2 + (25001 / 100000 : ℝ) := by
  intro x1 x2 x3 x4 x5 x6 x7 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4, hl5, hu5, hl6, hu6⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_14.result x1 x2 x3 x4 x5 x6 x7 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num) (by convert hl5 using 1 <;> norm_num) (by convert hu5 using 1 <;> norm_num) (by convert hl6 using 1 <;> norm_num) (by convert hu6 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_14_7_variable_magnetism
