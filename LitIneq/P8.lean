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

namespace Lean92.BoxPoly45_BoxPoly45_08

theorem result (x1 x2 x3 x4 x5 : ℝ) (hl0 : (-5 : ℝ) ≤ x1) (hu0 : x1 ≤ (5 : ℝ)) (hl1 : (-5 : ℝ) ≤ x2) (hu1 : x2 ≤ (5 : ℝ)) (hl2 : (-5 : ℝ) ≤ x3) (hu2 : x3 ≤ (5 : ℝ)) (hl3 : (-5 : ℝ) ≤ x4) (hu3 : x4 ≤ (5 : ℝ)) (hl4 : (-5 : ℝ) ≤ x5) (hu4 : x5 ≤ (5 : ℝ)) : (0 : ℝ) ≤ x1 + x2 + x3 + x4 + x5^2 - x5 + 30 := by
  have hcert : (0 : ℝ) ≤ (x1) + (x2) + (x3) + (x4) + ((x5)^2) + ((-1)*(x5)) + (30) := by
    have hgg1 : (0 : ℝ) ≤ (x1) + (5) := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ (29/25)*(1)^2 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg10 : (0 : ℝ) ≤ (5) + ((-1)*(x5)) := by first | positivity | nlinarith
    have hsg10 : (0 : ℝ) ≤ (2/5)*(1)^2 := by positivity
    have hpg10 := mul_nonneg hsg10 hgg10
    have hgg2 : (0 : ℝ) ≤ (5) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ (4/25)*(1)^2 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hgg3 : (0 : ℝ) ≤ (x2) + (5) := by first | positivity | nlinarith
    have hsg3 : (0 : ℝ) ≤ (29/25)*(1)^2 := by positivity
    have hpg3 := mul_nonneg hsg3 hgg3
    have hgg4 : (0 : ℝ) ≤ (5) + ((-1)*(x2)) := by first | positivity | nlinarith
    have hsg4 : (0 : ℝ) ≤ (4/25)*(1)^2 := by positivity
    have hpg4 := mul_nonneg hsg4 hgg4
    have hgg5 : (0 : ℝ) ≤ (x3) + (5) := by first | positivity | nlinarith
    have hsg5 : (0 : ℝ) ≤ (29/25)*(1)^2 := by positivity
    have hpg5 := mul_nonneg hsg5 hgg5
    have hgg6 : (0 : ℝ) ≤ (5) + ((-1)*(x3)) := by first | positivity | nlinarith
    have hsg6 : (0 : ℝ) ≤ (4/25)*(1)^2 := by positivity
    have hpg6 := mul_nonneg hsg6 hgg6
    have hgg7 : (0 : ℝ) ≤ (x4) + (5) := by first | positivity | nlinarith
    have hsg7 : (0 : ℝ) ≤ (29/25)*(1)^2 := by positivity
    have hpg7 := mul_nonneg hsg7 hgg7
    have hgg8 : (0 : ℝ) ≤ (5) + ((-1)*(x4)) := by first | positivity | nlinarith
    have hsg8 : (0 : ℝ) ≤ (4/25)*(1)^2 := by positivity
    have hpg8 := mul_nonneg hsg8 hgg8
    have hgg9 : (0 : ℝ) ≤ (x5) + (5) := by first | positivity | nlinarith
    have hsg9 : (0 : ℝ) ≤ (6/25)*(1)^2 := by positivity
    have hpg9 := mul_nonneg hsg9 hgg9
    have hs0 : (0 : ℝ) ≤ (5/2)*((2/5) - (21/50)*x5)^2 + (1000/559)*((559/1000)*x5)^2 := by positivity
    have hid : ((x1) + (x2) + (x3) + (x4) + ((x5)^2) + ((-1)*(x5)) + (30)) = (((5/2)*((2/5) - (21/50)*x5)^2 + (1000/559)*((559/1000)*x5)^2) + ((29/25)*(1)^2)*((x1) + (5)) + ((4/25)*(1)^2)*((5) + ((-1)*(x1))) + ((29/25)*(1)^2)*((x2) + (5)) + ((4/25)*(1)^2)*((5) + ((-1)*(x2))) + ((29/25)*(1)^2)*((x3) + (5)) + ((4/25)*(1)^2)*((5) + ((-1)*(x3))) + ((29/25)*(1)^2)*((x4) + (5)) + ((4/25)*(1)^2)*((5) + ((-1)*(x4))) + ((6/25)*(1)^2)*((x5) + (5)) + ((2/5)*(1)^2)*((5) + ((-1)*(x5)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring

end Lean92.BoxPoly45_BoxPoly45_08


set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 8
name: C8
source_status: confirmed_from_appirl_citation_and_code
basis: 285
paper_title: Finding all solutions to a system of polynomial equations
source_evidence: /home/ljh/APPIRL/proof/Example.py:82-86; /tmp/2503.06592v1.layout.txt:521-533; /tmp/2503.06592v1.layout.txt:537; /tmp/2503.06592v1.layout.txt:757-758

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_08_c8 :
    ∀ x1 x2 x3 x4 x5 : ℝ,
      -5 <= x1 ∧
      x1 <= 5 ∧
      -5 <= x2 ∧
      x2 <= 5 ∧
      -5 <= x3 ∧
      x3 <= 5 ∧
      -5 <= x4 ∧
      x4 <= 5 ∧
      -5 <= x5 ∧
      x5 <= 5 →
        0 <= x1 + x2 + x3 + x4 + x5^2 - x5 + 30 := by
  intro x1 x2 x3 x4 x5 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_08.result x1 x2 x3 x4 x5 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_08_c8
