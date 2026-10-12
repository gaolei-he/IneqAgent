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

namespace Lean92.BoxPoly45_BoxPoly45_41

theorem result (x1 x2 : ℝ) (hl0 : (-5 : ℝ) ≤ x1) (hu0 : x1 ≤ (5 : ℝ)) (hl1 : (-5 : ℝ) ≤ x2) (hu1 : x2 ≤ (5 : ℝ)) : (0 : ℝ) ≤ 170 + x1^4 + x2^4 - 22*x2 - 21*x1^2 - 14*x1 - 13*x2^2 + 2*x1*x2^2 + 2*x2*x1^2 := by
  have hcert : (0 : ℝ) ≤ ((x1)^4) + ((2)*((x1)^2)*(x2)) + ((-1)*(21)*((x1)^2)) + ((2)*(x1)*((x2)^2)) + ((-1)*(14)*(x1)) + ((x2)^4) + ((-1)*(13)*((x2)^2)) + ((-1)*(22)*(x2)) + (170) := by
    have hgg1 : (0 : ℝ) ≤ (x1) + (5) := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ 0 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg2 : (0 : ℝ) ≤ (5) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ 0 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hgg3 : (0 : ℝ) ≤ (x2) + (5) := by first | positivity | nlinarith
    have hsg3 : (0 : ℝ) ≤ 0 := by positivity
    have hpg3 := mul_nonneg hsg3 hgg3
    have hgg4 : (0 : ℝ) ≤ (5) + ((-1)*(x2)) := by first | positivity | nlinarith
    have hsg4 : (0 : ℝ) ≤ 0 := by positivity
    have hpg4 := mul_nonneg hsg4 hgg4
    have hs0 : (0 : ℝ) ≤ (1/170)*((170/1) - (7/1)*x1 - (11/1)*x2 - (11/1)*(x1^2) - (7/1)*(x2^2))^2 + (170/49)*(-(77/170)*x1 + (49/170)*x2 + (49/170)*(x1^2) - (77/170)*(x2^2))^2 + (0/1)*(0/1)^2 + (0/1)*(0/1)^2 + (0/1)*(0/1)^2 + (0/1)*(0/1)^2 := by positivity
    have hid : (((x1)^4) + ((2)*((x1)^2)*(x2)) + ((-1)*(21)*((x1)^2)) + ((2)*(x1)*((x2)^2)) + ((-1)*(14)*(x1)) + ((x2)^4) + ((-1)*(13)*((x2)^2)) + ((-1)*(22)*(x2)) + (170)) = (((1/170)*((170/1) - (7/1)*x1 - (11/1)*x2 - (11/1)*(x1^2) - (7/1)*(x2^2))^2 + (170/49)*(-(77/170)*x1 + (49/170)*x2 + (49/170)*(x1^2) - (77/170)*(x2^2))^2 + (0/1)*(0/1)^2 + (0/1)*(0/1)^2 + (0/1)*(0/1)^2 + (0/1)*(0/1)^2) + (0)*((x1) + (5)) + (0)*((5) + ((-1)*(x1))) + (0)*((x2) + (5)) + (0)*((5) + ((-1)*(x2)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring

end Lean92.BoxPoly45_BoxPoly45_41


set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 41
id: B03
name: Himmelblau
source_status: confirmed_transformed
paper_title: An efficient algorithm for range computation of polynomials using the Bernstein form
paper_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: (x1^2 + x2 - 11)^2 + (x1 + x2^2 - 7)^2
source_evidence: PDF DOI 10.1007/s10898-008-9382-y; Appendix B Problem 3

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_41_b03_himmelblau :
    ∀ x1 x2 : ℝ,
      -5 <= x1 ∧
      x1 <= 5 ∧
      -5 <= x2 ∧
      x2 <= 5 →
        0 <= 170 + x1^4 + x2^4 - 22*x2 - 21*x1^2 - 14*x1 - 13*x2^2 + 2*x1*x2^2 + 2*x2*x1^2 := by
  intro x1 x2 ⟨hl0, hu0, hl1, hu1⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_41.result x1 x2 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_41_b03_himmelblau
