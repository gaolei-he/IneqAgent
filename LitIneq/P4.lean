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

namespace Lean92.BoxPoly45_BoxPoly45_04

theorem result (x1 x2 : ℝ) (hl0 : (-1 : ℝ) ≤ x1) (hu0 : x1 ≤ (1 : ℝ)) (hl1 : (-1 : ℝ) ≤ x2) (hu1 : x2 ≤ (1 : ℝ)) : (0 : ℝ) ≤ x1^2 + 4*x2^2 + 167/100 := by
  have hcert : (0 : ℝ) ≤ ((x1)^2) + ((4)*((x2)^2)) + (167/100) := by
    have hgg1 : (0 : ℝ) ≤ (x1) + (1) := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ 0 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg2 : (0 : ℝ) ≤ (1) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ 0 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hgg3 : (0 : ℝ) ≤ (x2) + (1) := by first | positivity | nlinarith
    have hsg3 : (0 : ℝ) ≤ 0 := by positivity
    have hpg3 := mul_nonneg hsg3 hgg3
    have hgg4 : (0 : ℝ) ≤ (1) + ((-1)*(x2)) := by first | positivity | nlinarith
    have hsg4 : (0 : ℝ) ≤ 0 := by positivity
    have hpg4 := mul_nonneg hsg4 hgg4
    have hs0 : (0 : ℝ) ≤ (100/167)*(167/100)^2 + (1/4)*((4/1)*x2)^2 + (1/1)*(x1)^2 := by positivity
    have hid : (((x1)^2) + ((4)*((x2)^2)) + (167/100)) = (((100/167)*(167/100)^2 + (1/4)*((4/1)*x2)^2 + (1/1)*(x1)^2) + (0)*((x1) + (1)) + (0)*((1) + ((-1)*(x1))) + (0)*((x2) + (1)) + (0)*((1) + ((-1)*(x2)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring

end Lean92.BoxPoly45_BoxPoly45_04


set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 4
name: C2
source_status: confirmed_from_appirl_citation_and_code
basis: 34
paper_title: Polynomial homotopy continuation: A portable Ada software package
source_evidence: /home/ljh/APPIRL/proof/Example.py:38-42; /tmp/2503.06592v1.layout.txt:521-527; /tmp/2503.06592v1.layout.txt:537; /tmp/2503.06592v1.layout.txt:740-742

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_04_c2 :
    ∀ x1 x2 : ℝ,
      -1 <= x1 ∧
      x1 <= 1 ∧
      -1 <= x2 ∧
      x2 <= 1 →
        0 <= x1^2 + 4*x2^2 + (167 / 100 : ℝ) := by
  intro x1 x2 ⟨hl0, hu0, hl1, hu1⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_04.result x1 x2 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_04_c2
