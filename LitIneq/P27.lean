import Mathlib

set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 27
id: A07
name: Hun 5
reference: An efficient algorithm for range computation of polynomials using the Bernstein form
reference_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: x2^6*x3 + x2*x3^6 + x1^2*x2^4*x5 - 3*x1*x2^2*x3^2*x4*x5 + x3^4*x4^2*x5 - x1^3*x3*x4*x5^2 - x1*x2*x4^3*x5^2 + x2*x3*x5^5 + 1436515078155/1000000000
source_location: Table 1 Ex 7; Appendix A Problem 7

-/
theorem box_benchmark_27_a07_hun_5 :
    ∀ x1 x2 x3 x4 x5 : ℝ,
      0 <= x1 ∧
      x1 <= 1 ∧
      2 <= x2 ∧
      x2 <= 3 ∧
      -2 <= x3 ∧
      x3 <= -1 ∧
      1 <= x4 ∧
      x4 <= 3 ∧
      -2 <= x5 ∧
      x5 <= -1 →
        0 <= (287303015631 / 200000000 : ℝ) + x2*x3^6 + x3*x2^6 + x2*x3*x5^5 + x5*x1^2*x2^4 + x5*x3^4*x4^2 - 1*x1*x2*x4^3*x5^2 - 1*x3*x4*x1^3*x5^2 - 3*x1*x4*x5*x2^2*x3^2 := by
  sorry

end Leanpro.BoxJsonlWithSources
