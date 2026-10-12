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

namespace Lean92.BoxPoly45_BoxPoly45_45

theorem result (x1 x2 : ℝ) (hl0 : (-5 : ℝ) ≤ x1) (hu0 : x1 ≤ (10 : ℝ)) (hl1 : (-5 : ℝ) ≤ x2) (hu1 : x2 ≤ (10 : ℝ)) : (0 : ℝ) ≤ x2^4 + 2*x2^2 + 1/16*x1^4 + 5/4*x1^2 + x1*x2 + 1/2*x2*x1^3 + 2*x1*x2^3 + 3/2*x1^2*x2^2 := by
  have hcert : (0 : ℝ) ≤ ((1/16)*((x1)^4)) + ((1/2)*((x1)^3)*(x2)) + ((3/2)*((x1)^2)*((x2)^2)) + ((5/4)*((x1)^2)) + ((2)*(x1)*((x2)^3)) + ((x1)*(x2)) + ((x2)^4) + ((2)*((x2)^2)) := by
    have hgg1 : (0 : ℝ) ≤ (x1) + (5) := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ 0 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg2 : (0 : ℝ) ≤ (10) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ 0 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hgg3 : (0 : ℝ) ≤ (x2) + (5) := by first | positivity | nlinarith
    have hsg3 : (0 : ℝ) ≤ 0 := by positivity
    have hpg3 := mul_nonneg hsg3 hgg3
    have hgg4 : (0 : ℝ) ≤ (10) + ((-1)*(x2)) := by first | positivity | nlinarith
    have hsg4 : (0 : ℝ) ≤ 0 := by positivity
    have hpg4 := mul_nonneg hsg4 hgg4
    have hs0 : (0 : ℝ) ≤ (1/2)*((1/2)*x1 + (2/1)*x2)^2 + (8/9)*((9/8)*x1)^2 + (1/1)*((1/4)*(x1^2) + x1*x2 + x2^2)^2 + (0/1)*(0)^2 + (0/1)*(0)^2 := by positivity
    have hid : (((1/16)*((x1)^4)) + ((1/2)*((x1)^3)*(x2)) + ((3/2)*((x1)^2)*((x2)^2)) + ((5/4)*((x1)^2)) + ((2)*(x1)*((x2)^3)) + ((x1)*(x2)) + ((x2)^4) + ((2)*((x2)^2))) = (((1/2)*((1/2)*x1 + (2/1)*x2)^2 + (8/9)*((9/8)*x1)^2 + (1/1)*((1/4)*(x1^2) + x1*x2 + x2^2)^2 + (0/1)*(0)^2 + (0/1)*(0)^2) + (0)*((x1) + (5)) + (0)*((10) + ((-1)*(x1))) + (0)*((x2) + (5)) + (0)*((10) + ((-1)*(x2)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring

end Lean92.BoxPoly45_BoxPoly45_45


set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 45
id: B07
name: Zakharov n=2
source_status: confirmed_transformed
paper_title: An efficient algorithm for range computation of polynomials using the Bernstein form
paper_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: x1^2+x2^2 + (1/2*x1 + x2)^2 + (1/2*x1 + x2)^4
source_evidence: PDF DOI 10.1007/s10898-008-9382-y; Appendix B Problem 7

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_45_b07_zakharov_n_2 :
    ∀ x1 x2 : ℝ,
      -5 <= x1 ∧
      x1 <= 10 ∧
      -5 <= x2 ∧
      x2 <= 10 →
        0 <= x2^4 + 2*x2^2 + (1 / 16 : ℝ)*x1^4 + (5 / 4 : ℝ)*x1^2 + x1*x2 + (1 / 2 : ℝ)*x2*x1^3 + 2*x1*x2^3 + (3 / 2 : ℝ)*x1^2*x2^2 := by
  intro x1 x2 ⟨hl0, hu0, hl1, hu1⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_45.result x1 x2 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_45_b07_zakharov_n_2
