import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 x4 x5 : ℝ) (hl0 : (-1 : ℝ) ≤ x1) (hu0 : x1 ≤ (1 : ℝ)) (hl1 : (-1 : ℝ) ≤ x2) (hu1 : x2 ≤ (1 : ℝ)) (hl2 : (-1 : ℝ) ≤ x3) (hu2 : x3 ≤ (1 : ℝ)) (hl3 : (-1 : ℝ) ≤ x4) (hu3 : x4 ≤ (1 : ℝ)) (hl4 : (-1 : ℝ) ≤ x5) (hu4 : x5 ≤ (1 : ℝ)) : (0 : ℝ) ≤ 4 - 2*x2^6 - 2*x4^6 + 2*x1^6 + 2*x3^6 + 2*x5^6 := by
  have ha0 : |x1| ≤ (1 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha1 : |x2| ≤ (1 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha2 : |x3| ≤ (1 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha3 : |x4| ≤ (1 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha4 : |x5| ≤ (1 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ht0 : (0 : ℝ) ≤ x1^6 := by positivity
  have hb1 : |x2^6| ≤ (1 : ℝ) := by
    calc
      |x2^6| = |x2|^6 := by simp only [abs_mul, abs_pow]
      _ ≤ (1)^6 := by gcongr <;> assumption
      _ = (1 : ℝ) := by norm_num
  have ht1 := (abs_le.mp hb1).1
  have hu1 := (abs_le.mp hb1).2
  have ht2 : (0 : ℝ) ≤ x3^6 := by positivity
  have hb3 : |x4^6| ≤ (1 : ℝ) := by
    calc
      |x4^6| = |x4|^6 := by simp only [abs_mul, abs_pow]
      _ ≤ (1)^6 := by gcongr <;> assumption
      _ = (1 : ℝ) := by norm_num
  have ht3 := (abs_le.mp hb3).1
  have hu3 := (abs_le.mp hb3).2
  have ht4 : (0 : ℝ) ≤ x5^6 := by positivity
  nlinarith only [ht0, ht1, hu1, ht2, ht3, hu3, ht4]



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 26
id: A06
name: Reim 5
reference: An efficient algorithm for range computation of polynomials using the Bernstein form
reference_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: -1 + 2*x1^6 - 2*x2^6 + 2*x3^6 - 2*x4^6 + 2*x5^6 + 5
source_location: Table 1 Ex 6; Appendix A Problem 6

-/
theorem box_benchmark_26_a06_reim_5 :
    ∀ x1 x2 x3 x4 x5 : ℝ,
      -1 <= x1 ∧
      x1 <= 1 ∧
      -1 <= x2 ∧
      x2 <= 1 ∧
      -1 <= x3 ∧
      x3 <= 1 ∧
      -1 <= x4 ∧
      x4 <= 1 ∧
      -1 <= x5 ∧
      x5 <= 1 →
        0 <= 4 - 2*x2^6 - 2*x4^6 + 2*x1^6 + 2*x3^6 + 2*x5^6 := by
  intro x1 x2 x3 x4 x5 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4⟩
  have htranslated := @result x1 x2 x3 x4 x5 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
