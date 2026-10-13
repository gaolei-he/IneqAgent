import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 x4 x5 x6 : ℝ) (hl0 : (2 : ℝ) ≤ x1) (hu0 : x1 ≤ (5 : ℝ)) (hl1 : (2 : ℝ) ≤ x2) (hu1 : x2 ≤ (5 : ℝ)) (hl2 : (2 : ℝ) ≤ x3) (hu2 : x3 ≤ (5 : ℝ)) (hl3 : (-5 : ℝ) ≤ x4) (hu3 : x4 ≤ (-2 : ℝ)) (hl4 : (-5 : ℝ) ≤ x5) (hu4 : x5 ≤ (-2 : ℝ)) (hl5 : (-5 : ℝ) ≤ x6) (hu5 : x6 ≤ (-2 : ℝ)) : (0 : ℝ) ≤ 1875 + x4*x3^3 + x5*x2^3 + x6*x1^3 := by
  have ha0 : |x1| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha1 : |x2| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha2 : |x3| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha3 : |x4| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha4 : |x5| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha5 : |x6| ≤ (5 : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hb0 : |x1^3 * x6^1| ≤ (625 : ℝ) := by
    calc
      |x1^3 * x6^1| = |x1|^3 * |x6|^1 := by simp only [abs_mul, abs_pow]
      _ ≤ (5)^3 * (5)^1 := by gcongr <;> assumption
      _ = (625 : ℝ) := by norm_num
  have ht0 := (abs_le.mp hb0).1
  have hu0 := (abs_le.mp hb0).2
  have hb1 : |x2^3 * x5^1| ≤ (625 : ℝ) := by
    calc
      |x2^3 * x5^1| = |x2|^3 * |x5|^1 := by simp only [abs_mul, abs_pow]
      _ ≤ (5)^3 * (5)^1 := by gcongr <;> assumption
      _ = (625 : ℝ) := by norm_num
  have ht1 := (abs_le.mp hb1).1
  have hu1 := (abs_le.mp hb1).2
  have hb2 : |x3^3 * x4^1| ≤ (625 : ℝ) := by
    calc
      |x3^3 * x4^1| = |x3|^3 * |x4|^1 := by simp only [abs_mul, abs_pow]
      _ ≤ (5)^3 * (5)^1 := by gcongr <;> assumption
      _ = (625 : ℝ) := by norm_num
  have ht2 := (abs_le.mp hb2).1
  have hu2 := (abs_le.mp hb2).2
  nlinarith only [ht0, hu0, ht1, hu1, ht2, hu2]



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 32
id: A12
name: Hair 6
reference: An efficient algorithm for range computation of polynomials using the Bernstein form
reference_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: x3^3*x4 + x2^3*x5 + x1^3*x6 - 1/4 + 7501/4
source_location: Table 1 Ex 12; Appendix A Problem 12

-/
theorem box_benchmark_32_a12_hair_6 :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      2 <= x1 ∧
      x1 <= 5 ∧
      2 <= x2 ∧
      x2 <= 5 ∧
      2 <= x3 ∧
      x3 <= 5 ∧
      -5 <= x4 ∧
      x4 <= -2 ∧
      -5 <= x5 ∧
      x5 <= -2 ∧
      -5 <= x6 ∧
      x6 <= -2 →
        0 <= 1875 + x4*x3^3 + x5*x2^3 + x6*x1^3 := by
  intro x1 x2 x3 x4 x5 x6 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4, hl5, hu5⟩
  have htranslated := @result x1 x2 x3 x4 x5 x6 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num) (by convert hl5 using 1 <;> norm_num) (by convert hu5 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
