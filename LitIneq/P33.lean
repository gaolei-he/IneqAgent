import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.GCongr
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace Lean92.BoxPoly45_BoxPoly45_33

theorem result (x1 x2 x3 x4 x5 x6 : ℝ) (hl0 : (-5 : ℝ) ≤ x1) (hu0 : x1 ≤ (5 : ℝ)) (hl1 : (-5 : ℝ) ≤ x2) (hu1 : x2 ≤ (5 : ℝ)) (hl2 : (-5 : ℝ) ≤ x3) (hu2 : x3 ≤ (5 : ℝ)) (hl3 : (-5 : ℝ) ≤ x4) (hu3 : x4 ≤ (5 : ℝ)) (hl4 : (-5 : ℝ) ≤ x5) (hu4 : x5 ≤ (5 : ℝ)) (hl5 : (-5 : ℝ) ≤ x6) (hu5 : x6 ≤ (5 : ℝ)) : (0 : ℝ) ≤ 937500 - 2*x2^7 - 2*x4^7 - 2*x6^7 + 2*x1^7 + 2*x3^7 + 2*x5^7 := by
  have ha0 : |x1| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha1 : |x2| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha2 : |x3| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha3 : |x4| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha4 : |x5| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha5 : |x6| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb0 : |x1^7| ≤ (78125 : ℝ) := by
    calc
      |x1^7| = |x1|^7 := by simp only [abs_mul, abs_pow]
      _ ≤ (5)^7 := by gcongr <;> assumption
      _ = (78125 : ℝ) := by norm_num
  have ht0 := (abs_le.mp hb0).1
  have hu0 := (abs_le.mp hb0).2
  have hb1 : |x2^7| ≤ (78125 : ℝ) := by
    calc
      |x2^7| = |x2|^7 := by simp only [abs_mul, abs_pow]
      _ ≤ (5)^7 := by gcongr <;> assumption
      _ = (78125 : ℝ) := by norm_num
  have ht1 := (abs_le.mp hb1).1
  have hu1 := (abs_le.mp hb1).2
  have hb2 : |x3^7| ≤ (78125 : ℝ) := by
    calc
      |x3^7| = |x3|^7 := by simp only [abs_mul, abs_pow]
      _ ≤ (5)^7 := by gcongr <;> assumption
      _ = (78125 : ℝ) := by norm_num
  have ht2 := (abs_le.mp hb2).1
  have hu2 := (abs_le.mp hb2).2
  have hb3 : |x4^7| ≤ (78125 : ℝ) := by
    calc
      |x4^7| = |x4|^7 := by simp only [abs_mul, abs_pow]
      _ ≤ (5)^7 := by gcongr <;> assumption
      _ = (78125 : ℝ) := by norm_num
  have ht3 := (abs_le.mp hb3).1
  have hu3 := (abs_le.mp hb3).2
  have hb4 : |x5^7| ≤ (78125 : ℝ) := by
    calc
      |x5^7| = |x5|^7 := by simp only [abs_mul, abs_pow]
      _ ≤ (5)^7 := by gcongr <;> assumption
      _ = (78125 : ℝ) := by norm_num
  have ht4 := (abs_le.mp hb4).1
  have hu4 := (abs_le.mp hb4).2
  have hb5 : |x6^7| ≤ (78125 : ℝ) := by
    calc
      |x6^7| = |x6|^7 := by simp only [abs_mul, abs_pow]
      _ ≤ (5)^7 := by gcongr <;> assumption
      _ = (78125 : ℝ) := by norm_num
  have ht5 := (abs_le.mp hb5).1
  have hu5 := (abs_le.mp hb5).2
  nlinarith only [ht0, hu0, ht1, hu1, ht2, hu2, ht3, hu3, ht4, hu4, ht5, hu5]

end Lean92.BoxPoly45_BoxPoly45_33

open Real

set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 33
id: A13
name: Reim 6
source_status: confirmed_transformed
paper_title: An efficient algorithm for range computation of polynomials using the Bernstein form
paper_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: -1 + 2*x1^7 - 2*x2^7 + 2*x3^7 - 2*x4^7 + 2*x5^7 - 2*x6^7 + 937501
source_evidence: PDF DOI 10.1007/s10898-008-9382-y; Table 1 Ex 13; Appendix A Problem 13

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_33_a13_reim_6 :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      -5 <= x1 ∧
      x1 <= 5 ∧
      -5 <= x2 ∧
      x2 <= 5 ∧
      -5 <= x3 ∧
      x3 <= 5 ∧
      -5 <= x4 ∧
      x4 <= 5 ∧
      -5 <= x5 ∧
      x5 <= 5 ∧
      -5 <= x6 ∧
      x6 <= 5 →
        0 <= 937500 - 2*x2^7 - 2*x4^7 - 2*x6^7 + 2*x1^7 + 2*x3^7 + 2*x5^7 := by
  intro x1 x2 x3 x4 x5 x6 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4, hl5, hu5⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_33.result x1 x2 x3 x4 x5 x6 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num) (by convert hl5 using 1 <;> norm_num) (by convert hu5 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_33_a13_reim_6
