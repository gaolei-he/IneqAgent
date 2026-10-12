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

namespace Lean92.BoxPoly45_BoxPoly45_02

theorem result (x1 : ℝ) (hl0 : (0 : ℝ) ≤ x1) (hu0 : x1 ≤ (1 : ℝ)) : (0 : ℝ) ≤ 9*x1^2 - 6*x1 + 1 := by
  have hcert : (0 : ℝ) ≤ ((9)*((x1)^2)) + ((-1)*(6)*(x1)) + (1) := by
    have hgg1 : (0 : ℝ) ≤ x1 := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ 0 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg2 : (0 : ℝ) ≤ (1) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ 0 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hs0 : (0 : ℝ) ≤ (1/1)*(1 - (3/1)*x1)^2 + (0/1)*(0/1)^2 := by positivity
    have hid : (((9)*((x1)^2)) + ((-1)*(6)*(x1)) + (1)) = (((1/1)*(1 - (3/1)*x1)^2 + (0/1)*(0/1)^2) + (0)*(x1) + (0)*((1) + ((-1)*(x1)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring

end Lean92.BoxPoly45_BoxPoly45_02


set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 2
name: Bernstein subdivision termination example
source_status: confirmed
basis: 9
paper_title: Formalization of Bernstein Polynomials and Applications to Global Optimization
paper_url: https://doi.org/10.1007/s10817-012-9256-3
source_evidence: paper_examples_extract/bernstein.txt; paper_examples_extract/constrained_examples.json

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_02_bernstein_subdivision_termination_example :
    ∀ x1 : ℝ,
      0 <= x1 ∧
      x1 <= 1 →
        0 <= 9*x1^2 - 6*x1 + 1 := by
  intro x1 ⟨hl0, hu0⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_02.result x1 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_02_bernstein_subdivision_termination_example
