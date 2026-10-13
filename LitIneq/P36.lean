import Mathlib

set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 36
id: A16
name: Heart 8
reference: An efficient algorithm for range computation of polynomials using the Bernstein form
reference_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: x1*x6^3 - 3*x1*x6*x7^2 + x3*x7^3 - 3*x3*x7*x6^2 + x2*x5^3 - 3*x2*x5*x8^2 + x4*x8^3 - 3*x4*x8*x5^2 + 9563453/10000000 + 136775/100000
source_location: Table 1 Ex 16; Appendix A Problem 16

-/
theorem box_benchmark_36_a16_heart_8 :
    ∀ x1 x2 x3 x4 x5 x6 x7 x8 : ℝ,
      (-1 / 10 : ℝ) <= x1 ∧
      x1 <= (2 / 5 : ℝ) ∧
      (2 / 5 : ℝ) <= x2 ∧
      x2 <= 1 ∧
      (-7 / 10 : ℝ) <= x3 ∧
      x3 <= (-2 / 5 : ℝ) ∧
      (-7 / 10 : ℝ) <= x4 ∧
      x4 <= (2 / 5 : ℝ) ∧
      (1 / 10 : ℝ) <= x5 ∧
      x5 <= (1 / 5 : ℝ) ∧
      (-1 / 10 : ℝ) <= x6 ∧
      x6 <= (1 / 5 : ℝ) ∧
      (-3 / 10 : ℝ) <= x7 ∧
      x7 <= (11 / 10 : ℝ) ∧
      (-11 / 10 : ℝ) <= x8 ∧
      x8 <= (-3 / 10 : ℝ) →
        0 <= (23240953 / 10000000 : ℝ) + x1*x6^3 + x2*x5^3 + x3*x7^3 + x4*x8^3 - 3*x1*x6*x7^2 - 3*x2*x5*x8^2 - 3*x3*x7*x6^2 - 3*x4*x8*x5^2 := by
  sorry

end Leanpro.BoxJsonlWithSources
