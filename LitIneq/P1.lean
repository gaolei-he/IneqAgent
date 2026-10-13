import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 : ℝ) (hl0 : (0 : ℝ) ≤ x1) (hu0 : x1 ≤ (1 : ℝ)) : (0 : ℝ) ≤ 4*x1^2 - 4*x1 + 1 := by
  have hcert : (0 : ℝ) ≤ ((4)*((x1)^2)) + ((-1)*(4)*(x1)) + (1) := by
    have hgg1 : (0 : ℝ) ≤ x1 := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ 0 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg2 : (0 : ℝ) ≤ (1) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ 0 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hs0 : (0 : ℝ) ≤ (1/1)*(1 - (2/1)*x1)^2 + (0/1)*(0/1)^2 := by positivity
    have hid : (((4)*((x1)^2)) + ((-1)*(4)*(x1)) + (1)) = (((1/1)*(1 - (2/1)*x1)^2 + (0/1)*(0/1)^2) + (0)*(x1) + (0)*((1) + ((-1)*(x1)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 1
name: Bernstein coefficient example
reference: Formalization of Bernstein Polynomials and Applications to Global Optimization
reference_url: https://doi.org/10.1007/s10817-012-9256-3

-/
theorem box_benchmark_01_bernstein_coefficient_example :
    ∀ x1 : ℝ,
      0 <= x1 ∧
      x1 <= 1 →
        0 <= 4*x1^2 - 4*x1 + 1 := by
  intro x1 ⟨hl0, hu0⟩
  have htranslated := @result x1 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
