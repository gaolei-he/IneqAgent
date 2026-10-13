import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 x4 x5 x6 x7 x8 : ℝ) (hl0 : (-9999/100 : ℝ) ≤ x1) (hu0 : x1 ≤ (100 : ℝ)) (hl1 : (-9999/100 : ℝ) ≤ x2) (hu1 : x2 ≤ (100 : ℝ)) (hl2 : (-9999/100 : ℝ) ≤ x3) (hu2 : x3 ≤ (100 : ℝ)) (hl3 : (-9999/100 : ℝ) ≤ x4) (hu3 : x4 ≤ (100 : ℝ)) (hl4 : (-9999/100 : ℝ) ≤ x5) (hu4 : x5 ≤ (100 : ℝ)) (hl5 : (-9999/100 : ℝ) ≤ x6) (hu5 : x6 ≤ (100 : ℝ)) (hl6 : (-9999/100 : ℝ) ≤ x7) (hu6 : x7 ≤ (100 : ℝ)) (hl7 : (-9999/100 : ℝ) ≤ x8) (hu7 : x8 ≤ (100 : ℝ)) : (0 : ℝ) ≤ x1^2 + x2^2 + x3^2 + x4^2 + x5^2 + x6^2 + x7^2 + x8^2 := by
  have hcert : (0 : ℝ) ≤ ((x1)^2) + ((x2)^2) + ((x3)^2) + ((x4)^2) + ((x5)^2) + ((x6)^2) + ((x7)^2) + ((x8)^2) := by
    have hgg1 : (0 : ℝ) ≤ (x1) + (9999/100) := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ 0 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg10 : (0 : ℝ) ≤ (100) + ((-1)*(x5)) := by first | positivity | nlinarith
    have hsg10 : (0 : ℝ) ≤ 0 := by positivity
    have hpg10 := mul_nonneg hsg10 hgg10
    have hgg11 : (0 : ℝ) ≤ (x6) + (9999/100) := by first | positivity | nlinarith
    have hsg11 : (0 : ℝ) ≤ 0 := by positivity
    have hpg11 := mul_nonneg hsg11 hgg11
    have hgg12 : (0 : ℝ) ≤ (100) + ((-1)*(x6)) := by first | positivity | nlinarith
    have hsg12 : (0 : ℝ) ≤ 0 := by positivity
    have hpg12 := mul_nonneg hsg12 hgg12
    have hgg13 : (0 : ℝ) ≤ (x7) + (9999/100) := by first | positivity | nlinarith
    have hsg13 : (0 : ℝ) ≤ 0 := by positivity
    have hpg13 := mul_nonneg hsg13 hgg13
    have hgg14 : (0 : ℝ) ≤ (100) + ((-1)*(x7)) := by first | positivity | nlinarith
    have hsg14 : (0 : ℝ) ≤ 0 := by positivity
    have hpg14 := mul_nonneg hsg14 hgg14
    have hgg15 : (0 : ℝ) ≤ (x8) + (9999/100) := by first | positivity | nlinarith
    have hsg15 : (0 : ℝ) ≤ 0 := by positivity
    have hpg15 := mul_nonneg hsg15 hgg15
    have hgg16 : (0 : ℝ) ≤ (100) + ((-1)*(x8)) := by first | positivity | nlinarith
    have hsg16 : (0 : ℝ) ≤ 0 := by positivity
    have hpg16 := mul_nonneg hsg16 hgg16
    have hgg2 : (0 : ℝ) ≤ (100) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ 0 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hgg3 : (0 : ℝ) ≤ (x2) + (9999/100) := by first | positivity | nlinarith
    have hsg3 : (0 : ℝ) ≤ 0 := by positivity
    have hpg3 := mul_nonneg hsg3 hgg3
    have hgg4 : (0 : ℝ) ≤ (100) + ((-1)*(x2)) := by first | positivity | nlinarith
    have hsg4 : (0 : ℝ) ≤ 0 := by positivity
    have hpg4 := mul_nonneg hsg4 hgg4
    have hgg5 : (0 : ℝ) ≤ (x3) + (9999/100) := by first | positivity | nlinarith
    have hsg5 : (0 : ℝ) ≤ 0 := by positivity
    have hpg5 := mul_nonneg hsg5 hgg5
    have hgg6 : (0 : ℝ) ≤ (100) + ((-1)*(x3)) := by first | positivity | nlinarith
    have hsg6 : (0 : ℝ) ≤ 0 := by positivity
    have hpg6 := mul_nonneg hsg6 hgg6
    have hgg7 : (0 : ℝ) ≤ (x4) + (9999/100) := by first | positivity | nlinarith
    have hsg7 : (0 : ℝ) ≤ 0 := by positivity
    have hpg7 := mul_nonneg hsg7 hgg7
    have hgg8 : (0 : ℝ) ≤ (100) + ((-1)*(x4)) := by first | positivity | nlinarith
    have hsg8 : (0 : ℝ) ≤ 0 := by positivity
    have hpg8 := mul_nonneg hsg8 hgg8
    have hgg9 : (0 : ℝ) ≤ (x5) + (9999/100) := by first | positivity | nlinarith
    have hsg9 : (0 : ℝ) ≤ 0 := by positivity
    have hpg9 := mul_nonneg hsg9 hgg9
    have hs0 : (0 : ℝ) ≤ (1/1)*(x8)^2 + (1/1)*(x7)^2 + (1/1)*(x6)^2 + (1/1)*(x5)^2 + (1/1)*(x4)^2 + (1/1)*(x3)^2 + (1/1)*(x2)^2 + (1/1)*(x1)^2 := by positivity
    have hid : (((x1)^2) + ((x2)^2) + ((x3)^2) + ((x4)^2) + ((x5)^2) + ((x6)^2) + ((x7)^2) + ((x8)^2)) = (((1/1)*(x8)^2 + (1/1)*(x7)^2 + (1/1)*(x6)^2 + (1/1)*(x5)^2 + (1/1)*(x4)^2 + (1/1)*(x3)^2 + (1/1)*(x2)^2 + (1/1)*(x1)^2) + (0)*((x1) + (9999/100)) + (0)*((100) + ((-1)*(x1))) + (0)*((x2) + (9999/100)) + (0)*((100) + ((-1)*(x2))) + (0)*((x3) + (9999/100)) + (0)*((100) + ((-1)*(x3))) + (0)*((x4) + (9999/100)) + (0)*((100) + ((-1)*(x4))) + (0)*((x5) + (9999/100)) + (0)*((100) + ((-1)*(x5))) + (0)*((x6) + (9999/100)) + (0)*((100) + ((-1)*(x6))) + (0)*((x7) + (9999/100)) + (0)*((100) + ((-1)*(x7))) + (0)*((x8) + (9999/100)) + (0)*((100) + ((-1)*(x8)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 43
id: B05
name: Quadratic n=8 shifted
reference: An efficient algorithm for range computation of polynomials using the Bernstein form
reference_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: x1^2+x2^2+x3^2+x4^2+x5^2+x6^2+x7^2+x8^2
source_location: Appendix B Problem 5

-/
theorem box_benchmark_43_b05_quadratic_n_8_shifted :
    ∀ x1 x2 x3 x4 x5 x6 x7 x8 : ℝ,
      (-9999 / 100 : ℝ) <= x1 ∧
      x1 <= 100 ∧
      (-9999 / 100 : ℝ) <= x2 ∧
      x2 <= 100 ∧
      (-9999 / 100 : ℝ) <= x3 ∧
      x3 <= 100 ∧
      (-9999 / 100 : ℝ) <= x4 ∧
      x4 <= 100 ∧
      (-9999 / 100 : ℝ) <= x5 ∧
      x5 <= 100 ∧
      (-9999 / 100 : ℝ) <= x6 ∧
      x6 <= 100 ∧
      (-9999 / 100 : ℝ) <= x7 ∧
      x7 <= 100 ∧
      (-9999 / 100 : ℝ) <= x8 ∧
      x8 <= 100 →
        0 <= x1^2 + x2^2 + x3^2 + x4^2 + x5^2 + x6^2 + x7^2 + x8^2 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4, hl5, hu5, hl6, hu6, hl7, hu7⟩
  have htranslated := @result x1 x2 x3 x4 x5 x6 x7 x8 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num) (by convert hl5 using 1 <;> norm_num) (by convert hu5 using 1 <;> norm_num) (by convert hl6 using 1 <;> norm_num) (by convert hu6 using 1 <;> norm_num) (by convert hl7 using 1 <;> norm_num) (by convert hu7 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
