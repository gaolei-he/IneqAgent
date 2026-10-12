import Mathlib

set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 31
id: A11
name: But 6
source_status: confirmed_transformed
paper_title: An efficient algorithm for range computation of polynomials using the Bernstein form
paper_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: x6*x2^2 + x5*x3^2 - x1*x4^2 + x4^3 + x4^2 - 1/3*x1 + 4/3*x4 + 14393333333/10000000000
source_evidence: PDF DOI 10.1007/s10898-008-9382-y; Table 1 Ex 11; Appendix A Problem 11

The polynomial and constraints preserve the source expression and order.
The theorem constant uses the z3_adjustment above for an exact inequality.
-/
theorem box_benchmark_31_a11_but_6 :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      -1 <= x1 ∧
      x1 <= 0 ∧
      (-1 / 10 : ℝ) <= x2 ∧
      x2 <= (9 / 10 : ℝ) ∧
      (-1 / 10 : ℝ) <= x3 ∧
      x3 <= (1 / 2 : ℝ) ∧
      -1 <= x4 ∧
      x4 <= (-1 / 10 : ℝ) ∧
      (-1 / 10 : ℝ) <= x5 ∧
      x5 <= (-1 / 20 : ℝ) ∧
      (-1 / 10 : ℝ) <= x6 ∧
      x6 <= (-3 / 100 : ℝ) →
        0 <= (2159 / 1500 : ℝ) + x4^2 + x4^3 - (1 / 3 : ℝ)*x1 + (4 / 3 : ℝ)*x4 + x5*x3^2 + x6*x2^2 - 1*x1*x4^2 := by
  intro x1 x2 x3 x4 x5 x6 h
  obtain ⟨hx1a, hx1b, hx2a, hx2b, hx3a, hx3b,
          hx4a, hx4b, hx5a, hx5b, hx6a, hx6b⟩ := h
  -- Univariate x4 block: x4^3 + x4^2 + (4/3)x4 attains its minimum -4/3 at x4 = -1.
  have h4block : -(4/3 : ℝ) ≤ x4^3 + x4^2 + (4/3 : ℝ)*x4 := by
    have hx4p : 0 ≤ x4 + 1 := by linarith
    have hq : 0 ≤ x4^2 + (4/3 : ℝ) := by nlinarith [sq_nonneg x4]
    have hprod : 0 ≤ (x4 + 1) * (x4^2 + (4/3 : ℝ)) := mul_nonneg hx4p hq
    nlinarith [hprod]
  -- Range fact: x3^2 ≤ 1/4.
  have h3sq : x3^2 ≤ (1/4 : ℝ) := by
    have h1 : 0 ≤ (1/2 : ℝ) - x3 := by linarith
    have h2 : 0 ≤ x3 + (1/2 : ℝ) := by linarith
    nlinarith [mul_nonneg h1 h2]
  -- The x5*x3^2 block is bounded below by -1/40.
  have h5block : -(1/40 : ℝ) ≤ x5 * x3^2 := by
    have hsq : 0 ≤ x3^2 := sq_nonneg x3
    have hmul := mul_le_mul_of_nonneg_right hx5a hsq
    nlinarith [hmul, h3sq]
  -- Range fact: x2^2 ≤ 81/100.
  have h2sq : x2^2 ≤ (81/100 : ℝ) := by
    have h1 : 0 ≤ (9/10 : ℝ) - x2 := by linarith
    have h2 : 0 ≤ x2 + (9/10 : ℝ) := by linarith
    nlinarith [mul_nonneg h1 h2]
  -- The x6*x2^2 block is bounded below by -81/1000.
  have h6block : -(81/1000 : ℝ) ≤ x6 * x2^2 := by
    have hsq : 0 ≤ x2^2 := sq_nonneg x2
    have hmul := mul_le_mul_of_nonneg_right hx6a hsq
    nlinarith [hmul, h2sq]
  -- The x1 terms combine as -(1/3)x1 - x1*x4^2 = -x1*(1/3 + x4^2) ≥ 0.
  have h1block : 0 ≤ -(1/3 : ℝ)*x1 - x1*x4^2 := by
    have hx1n : 0 ≤ -x1 := by linarith
    have hc : 0 ≤ (1/3 : ℝ) + x4^2 := by nlinarith [sq_nonneg x4]
    have hprod : 0 ≤ (-x1) * ((1/3 : ℝ) + x4^2) := mul_nonneg hx1n hc
    nlinarith [hprod]
  -- The constant is exactly the sum of the four block deficits.
  have hconst : (2159/1500 : ℝ) - 4/3 - 1/40 - 81/1000 = 0 := by norm_num
  nlinarith [h4block, h5block, h6block, h1block, hconst]
