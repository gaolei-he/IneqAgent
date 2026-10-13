import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 x4 x5 x6 : ℝ) (hl0 : (-5 : ℝ) ≤ x1) (hu0 : x1 ≤ (5 : ℝ)) (hl1 : (-5 : ℝ) ≤ x2) (hu1 : x2 ≤ (5 : ℝ)) (hl2 : (-5 : ℝ) ≤ x3) (hu2 : x3 ≤ (5 : ℝ)) (hl3 : (-5 : ℝ) ≤ x4) (hu3 : x4 ≤ (5 : ℝ)) (hl4 : (-5 : ℝ) ≤ x5) (hu4 : x5 ≤ (5 : ℝ)) (hl5 : (-5 : ℝ) ≤ x6) (hu5 : x6 ≤ (5 : ℝ)) : (0 : ℝ) ≤ 1/4 + x6^2 - 1*x6 + 2*x1^2 + 2*x2^2 + 2*x3^2 + 2*x4^2 + 2*x5^2 := by
  have hcert : (0 : ℝ) ≤ ((2)*((x1)^2)) + ((2)*((x2)^2)) + ((2)*((x3)^2)) + ((2)*((x4)^2)) + ((2)*((x5)^2)) + ((x6)^2) + ((-1)*(x6)) + (1/4) := by
    have hgg1 : (0 : ℝ) ≤ (x1) + (5) := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ 0 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg10 : (0 : ℝ) ≤ (5) + ((-1)*(x5)) := by first | positivity | nlinarith
    have hsg10 : (0 : ℝ) ≤ 0 := by positivity
    have hpg10 := mul_nonneg hsg10 hgg10
    have hgg11 : (0 : ℝ) ≤ (x6) + (5) := by first | positivity | nlinarith
    have hsg11 : (0 : ℝ) ≤ 0 := by positivity
    have hpg11 := mul_nonneg hsg11 hgg11
    have hgg12 : (0 : ℝ) ≤ (5) + ((-1)*(x6)) := by first | positivity | nlinarith
    have hsg12 : (0 : ℝ) ≤ 0 := by positivity
    have hpg12 := mul_nonneg hsg12 hgg12
    have hgg2 : (0 : ℝ) ≤ (5) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ 0 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hgg3 : (0 : ℝ) ≤ (x2) + (5) := by first | positivity | nlinarith
    have hsg3 : (0 : ℝ) ≤ 0 := by positivity
    have hpg3 := mul_nonneg hsg3 hgg3
    have hgg4 : (0 : ℝ) ≤ (5) + ((-1)*(x2)) := by first | positivity | nlinarith
    have hsg4 : (0 : ℝ) ≤ 0 := by positivity
    have hpg4 := mul_nonneg hsg4 hgg4
    have hgg5 : (0 : ℝ) ≤ (x3) + (5) := by first | positivity | nlinarith
    have hsg5 : (0 : ℝ) ≤ 0 := by positivity
    have hpg5 := mul_nonneg hsg5 hgg5
    have hgg6 : (0 : ℝ) ≤ (5) + ((-1)*(x3)) := by first | positivity | nlinarith
    have hsg6 : (0 : ℝ) ≤ 0 := by positivity
    have hpg6 := mul_nonneg hsg6 hgg6
    have hgg7 : (0 : ℝ) ≤ (x4) + (5) := by first | positivity | nlinarith
    have hsg7 : (0 : ℝ) ≤ 0 := by positivity
    have hpg7 := mul_nonneg hsg7 hgg7
    have hgg8 : (0 : ℝ) ≤ (5) + ((-1)*(x4)) := by first | positivity | nlinarith
    have hsg8 : (0 : ℝ) ≤ 0 := by positivity
    have hpg8 := mul_nonneg hsg8 hgg8
    have hgg9 : (0 : ℝ) ≤ (x5) + (5) := by first | positivity | nlinarith
    have hsg9 : (0 : ℝ) ≤ 0 := by positivity
    have hpg9 := mul_nonneg hsg9 hgg9
    have hs0 : (0 : ℝ) ≤ (4/1)*((1/4) - (1/2)*x6)^2 + (0/1)*(0/1)^2 + (1/2)*((2/1)*x5)^2 + (1/2)*((2/1)*x4)^2 + (1/2)*((2/1)*x3)^2 + (1/2)*((2/1)*x2)^2 + (1/2)*((2/1)*x1)^2 := by positivity
    have hid : (((2)*((x1)^2)) + ((2)*((x2)^2)) + ((2)*((x3)^2)) + ((2)*((x4)^2)) + ((2)*((x5)^2)) + ((x6)^2) + ((-1)*(x6)) + (1/4)) = (((4/1)*((1/4) - (1/2)*x6)^2 + (0/1)*(0/1)^2 + (1/2)*((2/1)*x5)^2 + (1/2)*((2/1)*x4)^2 + (1/2)*((2/1)*x3)^2 + (1/2)*((2/1)*x2)^2 + (1/2)*((2/1)*x1)^2) + (0)*((x1) + (5)) + (0)*((5) + ((-1)*(x1))) + (0)*((x2) + (5)) + (0)*((5) + ((-1)*(x2))) + (0)*((x3) + (5)) + (0)*((5) + ((-1)*(x3))) + (0)*((x4) + (5)) + (0)*((5) + ((-1)*(x4))) + (0)*((x5) + (5)) + (0)*((5) + ((-1)*(x5))) + (0)*((x6) + (5)) + (0)*((5) + ((-1)*(x6)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 29
id: A09
name: Mag 6
reference: An efficient algorithm for range computation of polynomials using the Bernstein form
reference_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: 2*x1^2+2*x2^2+2*x3^2+2*x4^2+2*x5^2+x6^2-x6+1/4
source_location: Table 1 Ex 9; Appendix A Problem 9

-/
theorem box_benchmark_29_a09_mag_6 :
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
        0 <= (1 / 4 : ℝ) + x6^2 - 1*x6 + 2*x1^2 + 2*x2^2 + 2*x3^2 + 2*x4^2 + 2*x5^2 := by
  intro x1 x2 x3 x4 x5 x6 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4, hl5, hu5⟩
  have htranslated := @result x1 x2 x3 x4 x5 x6 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num) (by convert hl5 using 1 <;> norm_num) (by convert hu5 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
