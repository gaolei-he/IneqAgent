import Mathlib

set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 40
id: B02
name: Six-hump camel shifted
reference: An efficient algorithm for range computation of polynomials using the Bernstein form
reference_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: 4*x1^2 - 21/10*x1^4 + 1/3*x1^6 + x1*x2 - 4*x2^2 + 4*x2^4 + 1031628453489616/1000000000000000
note: Uses decimal approximation of the reported minimum.
source_location: Appendix B Problem 2

The polynomial and constraints preserve the source expression and order.
The constant is adjusted from original_f, as recorded in the benchmark catalog.
-/
theorem box_benchmark_40_b02_six_hump_camel_shifted :
    ∀ x1 x2 : ℝ,
      -3 <= x1 ∧
      x1 <= 3 ∧
      -3 <= x2 ∧
      x2 <= 3 →
        0 <= (20632569069797547008327308743 / 20000000000000000000000000000 : ℝ) - 4*x2^2 + 4*x1^2 + 4*x2^4 - (21 / 10 : ℝ)*x1^4 + (1 / 3 : ℝ)*x1^6 + x1*x2 := by
  sorry

end Leanpro.BoxJsonlWithSources
