import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 : ℝ) (hl0 : (-10 : ℝ) ≤ x1) (hu0 : x1 ≤ (10 : ℝ)) (hl1 : (-10 : ℝ) ≤ x2) (hu1 : x2 ≤ (10 : ℝ)) (hl2 : (-10 : ℝ) ≤ x3) (hu2 : x3 ≤ (10 : ℝ)) : (0 : ℝ) ≤ 2*x1^2 - 2*x1*x2^2 - 2*x1*x3^2 + x2^4 + x2^2 - 2*x2 + x3^4 + x3^2 - 2*x3 + 100000000029403/50000000000000 := by
  have hcert : (0 : ℝ) ≤ ((2)*((x1)^2)) + ((-1)*(2)*(x1)*((x2)^2)) + ((-1)*(2)*(x1)*((x3)^2)) + ((x2)^4) + ((x2)^2) + ((-1)*(2)*(x2)) + ((x3)^4) + ((x3)^2) + ((-1)*(2)*(x3)) + (100000000029403/50000000000000) := by
    have hgg1 : (0 : ℝ) ≤ (x1) + (10) := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ 0 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg2 : (0 : ℝ) ≤ (10) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ 0 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hgg3 : (0 : ℝ) ≤ (x2) + (10) := by first | positivity | nlinarith
    have hsg3 : (0 : ℝ) ≤ 0 := by positivity
    have hpg3 := mul_nonneg hsg3 hgg3
    have hgg4 : (0 : ℝ) ≤ (10) + ((-1)*(x2)) := by first | positivity | nlinarith
    have hsg4 : (0 : ℝ) ≤ 0 := by positivity
    have hpg4 := mul_nonneg hsg4 hgg4
    have hgg5 : (0 : ℝ) ≤ (x3) + (10) := by first | positivity | nlinarith
    have hsg5 : (0 : ℝ) ≤ 0 := by positivity
    have hpg5 := mul_nonneg hsg5 hgg5
    have hgg6 : (0 : ℝ) ≤ (10) + ((-1)*(x3)) := by first | positivity | nlinarith
    have hsg6 : (0 : ℝ) ≤ 0 := by positivity
    have hpg6 := mul_nonneg hsg6 hgg6
    have hs0 : (0 : ℝ) ≤ (50000000000000/100000000029403)*((100000000029403/50000000000000) - x2 - x3)^2 + (100000000029403/50000000029403)*(-(50000000000000/100000000029403)*x2 + (50000000029403/100000000029403)*x3)^2 + (50000000029403/29403)*((29403/50000000029403)*x2)^2 + (1/2)*((2/1)*x1 - (x2^2) - (x3^2))^2 + (2/1)*(-(1/2)*(x2^2) + (1/2)*(x3^2))^2 + (0/1)*(0/1)^2 + (0/1)*(0/1)^2 := by positivity
    have hid : (((2)*((x1)^2)) + ((-1)*(2)*(x1)*((x2)^2)) + ((-1)*(2)*(x1)*((x3)^2)) + ((x2)^4) + ((x2)^2) + ((-1)*(2)*(x2)) + ((x3)^4) + ((x3)^2) + ((-1)*(2)*(x3)) + (100000000029403/50000000000000)) = (((50000000000000/100000000029403)*((100000000029403/50000000000000) - x2 - x3)^2 + (100000000029403/50000000029403)*(-(50000000000000/100000000029403)*x2 + (50000000029403/100000000029403)*x3)^2 + (50000000029403/29403)*((29403/50000000029403)*x2)^2 + (1/2)*((2/1)*x1 - (x2^2) - (x3^2))^2 + (2/1)*(-(1/2)*(x2^2) + (1/2)*(x3^2))^2 + (0/1)*(0/1)^2 + (0/1)*(0/1)^2) + (0)*((x1) + (10)) + (0)*((10) + ((-1)*(x1))) + (0)*((x2) + (10)) + (0)*((10) + ((-1)*(x2))) + (0)*((x3) + (10)) + (0)*((10) + ((-1)*(x3)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 10
name: Schwefel
reference: Formalization of Bernstein Polynomials and Applications to Global Optimization / A Tool for Formal Verification of Nonlinear Inequalities
reference_url: https://doi.org/10.1007/s10817-012-9256-3

-/
theorem box_benchmark_10_schwefel :
    ∀ x1 x2 x3 : ℝ,
      -10 <= x1 ∧
      x1 <= 10 ∧
      -10 <= x2 ∧
      x2 <= 10 ∧
      -10 <= x3 ∧
      x3 <= 10 →
        0 <= 2*x1^2 - 2*x1*x2^2 - 2*x1*x3^2 + x2^4 + x2^2 - 2*x2 + x3^4 + x3^2 - 2*x3 + (100000000029403 / 50000000000000 : ℝ) := by
  intro x1 x2 x3 ⟨hl0, hu0, hl1, hu1, hl2, hu2⟩
  have htranslated := @result x1 x2 x3 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
