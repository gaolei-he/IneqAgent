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

namespace Lean92.BoxPoly45_BoxPoly45_42

theorem result (x1 x2 x3 x4 : ℝ) (hl0 : (-2 : ℝ) ≤ x1) (hu0 : x1 ≤ (2 : ℝ)) (hl1 : (-2 : ℝ) ≤ x2) (hu1 : x2 ≤ (2 : ℝ)) (hl2 : (-2 : ℝ) ≤ x3) (hu2 : x3 ≤ (2 : ℝ)) (hl3 : (-2 : ℝ) ≤ x4) (hu3 : x4 ≤ (2 : ℝ)) : (0 : ℝ) ≤ x1^2 + x1^4 + x2^2 + x2^4 + x3^2 + x3^4 + x4^2 + x4^4 - 2*x1*x4^2 - 2*x2*x1^2 - 2*x3*x2^2 - 2*x4*x3^2 := by
  have hcert : (0 : ℝ) ≤ ((x1)^4) + ((-1)*(2)*((x1)^2)*(x2)) + ((x1)^2) + ((-1)*(2)*(x1)*((x4)^2)) + ((x2)^4) + ((-1)*(2)*((x2)^2)*(x3)) + ((x2)^2) + ((x3)^4) + ((-1)*(2)*((x3)^2)*(x4)) + ((x3)^2) + ((x4)^4) + ((x4)^2) := by
    have hgg1 : (0 : ℝ) ≤ (x1) + (2) := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ 0 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg2 : (0 : ℝ) ≤ (2) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ 0 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hgg3 : (0 : ℝ) ≤ (x2) + (2) := by first | positivity | nlinarith
    have hsg3 : (0 : ℝ) ≤ 0 := by positivity
    have hpg3 := mul_nonneg hsg3 hgg3
    have hgg4 : (0 : ℝ) ≤ (2) + ((-1)*(x2)) := by first | positivity | nlinarith
    have hsg4 : (0 : ℝ) ≤ 0 := by positivity
    have hpg4 := mul_nonneg hsg4 hgg4
    have hgg5 : (0 : ℝ) ≤ (x3) + (2) := by first | positivity | nlinarith
    have hsg5 : (0 : ℝ) ≤ 0 := by positivity
    have hpg5 := mul_nonneg hsg5 hgg5
    have hgg6 : (0 : ℝ) ≤ (2) + ((-1)*(x3)) := by first | positivity | nlinarith
    have hsg6 : (0 : ℝ) ≤ 0 := by positivity
    have hpg6 := mul_nonneg hsg6 hgg6
    have hgg7 : (0 : ℝ) ≤ (x4) + (2) := by first | positivity | nlinarith
    have hsg7 : (0 : ℝ) ≤ 0 := by positivity
    have hpg7 := mul_nonneg hsg7 hgg7
    have hgg8 : (0 : ℝ) ≤ (2) + ((-1)*(x4)) := by first | positivity | nlinarith
    have hsg8 : (0 : ℝ) ≤ 0 := by positivity
    have hpg8 := mul_nonneg hsg8 hgg8
    have hs0 : (0 : ℝ) ≤ (1/1)*(x4 + (1/11)*(x1^2) - (5/11)*x1*x4 + (1/11)*(x2^2) - (1/11)*x2*x4 - (6/11)*(x3^2) - (1/11)*x3*x4)^2 + (1/1)*(x3 + (1/11)*(x1^2) - (1/11)*x1*x3 - (6/11)*(x2^2) - (1/11)*x2*x3 - (5/11)*x3*x4 + (1/11)*(x4^2))^2 + (1/1)*(x2 - (6/11)*(x1^2) - (1/11)*x1*x2 - (5/11)*x2*x3 - (1/11)*x2*x4 + (1/11)*(x3^2) + (1/11)*(x4^2))^2 + (1/1)*(x1 - (5/11)*x1*x2 - (1/11)*x1*x3 - (1/11)*x1*x4 + (1/11)*(x2^2) + (1/11)*(x3^2) - (6/11)*(x4^2))^2 + (121/83)*(-(28/121)*(x1^2) - (18/121)*x1*x2 - (5/121)*x1*x3 - (6/121)*x1*x4 - (10/121)*(x2^2) + (6/121)*x2*x3 + (1/121)*x2*x4 - (28/121)*(x3^2) + (5/121)*x3*x4 + (83/121)*(x4^2))^2 + (10043/3295)*((58/913)*(x1^2) + (90/10043)*x1*x2 - (1303/10043)*x1*x3 - (35/913)*x1*x4 - (1444/10043)*(x2^2) - (445/10043)*x2*x3 - (8/913)*x2*x4 - (358/10043)*(x3^2) + (3295/10043)*x3*x4)^2 + (398695/240817)*(-(61322/398695)*(x1^2) + (30/79739)*x1*x2 - (7883/398695)*x1*x3 - (13528/79739)*x1*x4 - (9964/36245)*(x2^2) + (4245/79739)*x2*x3 - (15743/398695)*x2*x4 + (240817/398695)*(x3^2))^2 + (29138857/10029376)*(-(1366395/29138857)*(x1^2) - (180901/29138857)*x1*x2 - (11284/2648987)*x1*x3 - (4188670/29138857)*x1*x4 - (365733/29138857)*(x2^2) - (3803553/29138857)*x2*x3 + (10029376/29138857)*x2*x4)^2 + (110323136/29435821)*(-(14086081/110323136)*(x1^2) - (500329/15760448)*x1*x2 - (8121/358192)*x1*x3 - (2270189/55161568)*x1*x4 - (4805791/110323136)*(x2^2) + (29435821/110323136)*x2*x3)^2 + (323794031/155516093)*(-(104910328/323794031)*(x1^2) + (7152144/323794031)*x1*x2 - (37564914/323794031)*x1*x3 - (20192995/323794031)*x1*x4 + (155516093/323794031)*(x2^2))^2 + (155516093/31162632)*(-(158293294/1710677023)*(x1^2) - (95019080/1710677023)*x1*x2 - (89476578/1710677023)*x1*x3 + (31162632/155516093)*x1*x4)^2 + (314223206/78244467)*(-(31244769/314223206)*(x1^2) - (23499849/157111603)*x1*x2 + (78244467/314223206)*x1*x3)^2 + (3107181/583916)*(-(583916/3107181)*(x1^2) + (583916/3107181)*x1*x2)^2 + (0/1)*(0)^2 := by positivity
    have hid : (((x1)^4) + ((-1)*(2)*((x1)^2)*(x2)) + ((x1)^2) + ((-1)*(2)*(x1)*((x4)^2)) + ((x2)^4) + ((-1)*(2)*((x2)^2)*(x3)) + ((x2)^2) + ((x3)^4) + ((-1)*(2)*((x3)^2)*(x4)) + ((x3)^2) + ((x4)^4) + ((x4)^2)) = (((1/1)*(x4 + (1/11)*(x1^2) - (5/11)*x1*x4 + (1/11)*(x2^2) - (1/11)*x2*x4 - (6/11)*(x3^2) - (1/11)*x3*x4)^2 + (1/1)*(x3 + (1/11)*(x1^2) - (1/11)*x1*x3 - (6/11)*(x2^2) - (1/11)*x2*x3 - (5/11)*x3*x4 + (1/11)*(x4^2))^2 + (1/1)*(x2 - (6/11)*(x1^2) - (1/11)*x1*x2 - (5/11)*x2*x3 - (1/11)*x2*x4 + (1/11)*(x3^2) + (1/11)*(x4^2))^2 + (1/1)*(x1 - (5/11)*x1*x2 - (1/11)*x1*x3 - (1/11)*x1*x4 + (1/11)*(x2^2) + (1/11)*(x3^2) - (6/11)*(x4^2))^2 + (121/83)*(-(28/121)*(x1^2) - (18/121)*x1*x2 - (5/121)*x1*x3 - (6/121)*x1*x4 - (10/121)*(x2^2) + (6/121)*x2*x3 + (1/121)*x2*x4 - (28/121)*(x3^2) + (5/121)*x3*x4 + (83/121)*(x4^2))^2 + (10043/3295)*((58/913)*(x1^2) + (90/10043)*x1*x2 - (1303/10043)*x1*x3 - (35/913)*x1*x4 - (1444/10043)*(x2^2) - (445/10043)*x2*x3 - (8/913)*x2*x4 - (358/10043)*(x3^2) + (3295/10043)*x3*x4)^2 + (398695/240817)*(-(61322/398695)*(x1^2) + (30/79739)*x1*x2 - (7883/398695)*x1*x3 - (13528/79739)*x1*x4 - (9964/36245)*(x2^2) + (4245/79739)*x2*x3 - (15743/398695)*x2*x4 + (240817/398695)*(x3^2))^2 + (29138857/10029376)*(-(1366395/29138857)*(x1^2) - (180901/29138857)*x1*x2 - (11284/2648987)*x1*x3 - (4188670/29138857)*x1*x4 - (365733/29138857)*(x2^2) - (3803553/29138857)*x2*x3 + (10029376/29138857)*x2*x4)^2 + (110323136/29435821)*(-(14086081/110323136)*(x1^2) - (500329/15760448)*x1*x2 - (8121/358192)*x1*x3 - (2270189/55161568)*x1*x4 - (4805791/110323136)*(x2^2) + (29435821/110323136)*x2*x3)^2 + (323794031/155516093)*(-(104910328/323794031)*(x1^2) + (7152144/323794031)*x1*x2 - (37564914/323794031)*x1*x3 - (20192995/323794031)*x1*x4 + (155516093/323794031)*(x2^2))^2 + (155516093/31162632)*(-(158293294/1710677023)*(x1^2) - (95019080/1710677023)*x1*x2 - (89476578/1710677023)*x1*x3 + (31162632/155516093)*x1*x4)^2 + (314223206/78244467)*(-(31244769/314223206)*(x1^2) - (23499849/157111603)*x1*x2 + (78244467/314223206)*x1*x3)^2 + (3107181/583916)*(-(583916/3107181)*(x1^2) + (583916/3107181)*x1*x2)^2 + (0/1)*(0)^2) + (0)*((x1) + (2)) + (0)*((2) + ((-1)*(x1))) + (0)*((x2) + (2)) + (0)*((2) + ((-1)*(x2))) + (0)*((x3) + (2)) + (0)*((2) + ((-1)*(x3))) + (0)*((x4) + (2)) + (0)*((2) + ((-1)*(x4)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring

end Lean92.BoxPoly45_BoxPoly45_42


set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 42
id: B04
name: Extended Kearfott n=4
source_status: confirmed_transformed
paper_title: An efficient algorithm for range computation of polynomials using the Bernstein form
paper_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: (x1^2-x2)^2 + (x2^2-x3)^2 + (x3^2-x4)^2 + (x4^2-x1)^2
source_evidence: PDF DOI 10.1007/s10898-008-9382-y; Appendix B Problem 4

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_42_b04_extended_kearfott_n_4 :
    ∀ x1 x2 x3 x4 : ℝ,
      -2 <= x1 ∧
      x1 <= 2 ∧
      -2 <= x2 ∧
      x2 <= 2 ∧
      -2 <= x3 ∧
      x3 <= 2 ∧
      -2 <= x4 ∧
      x4 <= 2 →
        0 <= x1^2 + x1^4 + x2^2 + x2^4 + x3^2 + x3^4 + x4^2 + x4^4 - 2*x1*x4^2 - 2*x2*x1^2 - 2*x3*x2^2 - 2*x4*x3^2 := by
  intro x1 x2 x3 x4 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_42.result x1 x2 x3 x4 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_42_b04_extended_kearfott_n_4
