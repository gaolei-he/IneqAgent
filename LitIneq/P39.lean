import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert
import Mathlib.Tactic.IntervalCases
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace Lean92.BoxPoly45_BoxPoly45_39

theorem result (x1 x2 : ℝ) (hl0 : (-2 : ℝ) ≤ x1) (hu0 : x1 ≤ (2 : ℝ)) (hl1 : (-2 : ℝ) ≤ x2) (hu1 : x2 ≤ (2 : ℝ)) : (0 : ℝ) ≤ 597 - 4428*x2^6 - 2454*x1^4 - 1072*x1^3 - 768*x1^7 - 648*x2^7 + 144*x1^8 + 720*x1 + 720*x2 + 729*x2^8 + 952*x1^6 + 1260*x1^2 + 1344*x1^5 + 1944*x2^5 + 3060*x2^2 + 12288*x2^3 + 14346*x2^4 - 23616*x1*x2^3 - 19296*x1*x2^2 - 11880*x1*x2^4 - 7680*x2*x1^4 - 5370*x1^4*x2^2 - 4680*x1*x2 - 4080*x1^4*x2^3 - 3480*x1^3*x2^4 - 1836*x1^3*x2^5 - 1458*x1^2*x2^6 - 1188*x1*x2^5 - 648*x1^6*x2^2 - 288*x2*x1^7 - 168*x2*x1^5 + 972*x1*x2^7 + 1224*x1^5*x2^3 + 1240*x1^3*x2^3 + 1305*x1^4*x2^4 + 1344*x2*x1^6 + 1944*x1*x2^6 + 2592*x1^5*x2^2 + 3672*x1^2*x2^5 + 5040*x1^2*x2^3 + 5784*x2*x1^3 + 7344*x2*x1^2 + 7776*x1^2*x2^2 + 8730*x1^2*x2^4 + 9840*x1^3*x2^2 := by
  have hid : (597 - 4428*x2^6 - 2454*x1^4 - 1072*x1^3 - 768*x1^7 - 648*x2^7 + 144*x1^8 + 720*x1 + 720*x2 + 729*x2^8 + 952*x1^6 + 1260*x1^2 + 1344*x1^5 + 1944*x2^5 + 3060*x2^2 + 12288*x2^3 + 14346*x2^4 - 23616*x1*x2^3 - 19296*x1*x2^2 - 11880*x1*x2^4 - 7680*x2*x1^4 - 5370*x1^4*x2^2 - 4680*x1*x2 - 4080*x1^4*x2^3 - 3480*x1^3*x2^4 - 1836*x1^3*x2^5 - 1458*x1^2*x2^6 - 1188*x1*x2^5 - 648*x1^6*x2^2 - 288*x2*x1^7 - 168*x2*x1^5 + 972*x1*x2^7 + 1224*x1^5*x2^3 + 1240*x1^3*x2^3 + 1305*x1^4*x2^4 + 1344*x2*x1^6 + 1944*x1*x2^6 + 2592*x1^5*x2^2 + 3672*x1^2*x2^5 + 5040*x1^2*x2^3 + 5784*x2*x1^3 + 7344*x2*x1^2 + 7776*x1^2*x2^2 + 8730*x1^2*x2^4 + 9840*x1^3*x2^2) = (((x1+x2+1)^2 * (3*((x1+x2+1)-10/3)^2+8/3)) * (3+(((2*x1-3*x2)-3)^2*(3*((2*x1-3*x2)+1/3)^2+8/3))) + (((2*x1-3*x2)-3)^2*(3*((2*x1-3*x2)+1/3)^2+8/3))) := by ring
  rw [hid]
  positivity

end Lean92.BoxPoly45_BoxPoly45_39


set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 39
id: B01
name: Goldstein-Price minus 3
source_status: confirmed_transformed
paper_title: An efficient algorithm for range computation of polynomials using the Bernstein form
paper_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: (1 + (x1+x2+1)^2*(19 - 14*x1 + 3*x1^2 - 14*x2 + 6*x1*x2 + 3*x2^2))*(30 + (2*x1-3*x2)^2*(18 - 32*x1 + 12*x1^2 + 48*x2 - 36*x1*x2 + 27*x2^2)) - 3
source_evidence: PDF DOI 10.1007/s10898-008-9382-y; Appendix B Problem 1

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_39_b01_goldstein_price_minus_3 :
    ∀ x1 x2 : ℝ,
      -2 <= x1 ∧
      x1 <= 2 ∧
      -2 <= x2 ∧
      x2 <= 2 →
        0 <= 597 - 4428*x2^6 - 2454*x1^4 - 1072*x1^3 - 768*x1^7 - 648*x2^7 + 144*x1^8 + 720*x1 + 720*x2 + 729*x2^8 + 952*x1^6 + 1260*x1^2 + 1344*x1^5 + 1944*x2^5 + 3060*x2^2 + 12288*x2^3 + 14346*x2^4 - 23616*x1*x2^3 - 19296*x1*x2^2 - 11880*x1*x2^4 - 7680*x2*x1^4 - 5370*x1^4*x2^2 - 4680*x1*x2 - 4080*x1^4*x2^3 - 3480*x1^3*x2^4 - 1836*x1^3*x2^5 - 1458*x1^2*x2^6 - 1188*x1*x2^5 - 648*x1^6*x2^2 - 288*x2*x1^7 - 168*x2*x1^5 + 972*x1*x2^7 + 1224*x1^5*x2^3 + 1240*x1^3*x2^3 + 1305*x1^4*x2^4 + 1344*x2*x1^6 + 1944*x1*x2^6 + 2592*x1^5*x2^2 + 3672*x1^2*x2^5 + 5040*x1^2*x2^3 + 5784*x2*x1^3 + 7344*x2*x1^2 + 7776*x1^2*x2^2 + 8730*x1^2*x2^4 + 9840*x1^3*x2^2 := by
  intro x1 x2 ⟨hl0, hu0, hl1, hu1⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_39.result x1 x2 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_39_b01_goldstein_price_minus_3
