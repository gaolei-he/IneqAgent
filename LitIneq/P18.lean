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

namespace Lean92.BoxPoly45_BoxPoly45_18

theorem result (x1 x2 x3 x4 x5 x6 : ℝ) (hl0 : (-1 : ℝ) ≤ x1) (hu0 : x1 ≤ (0 : ℝ)) (hl1 : (-1/10 : ℝ) ≤ x2) (hu1 : x2 ≤ (9/10 : ℝ)) (hl2 : (-1/10 : ℝ) ≤ x3) (hu2 : x3 ≤ (1/2 : ℝ)) (hl3 : (-1 : ℝ) ≤ x4) (hu3 : x4 ≤ (-1/10 : ℝ)) (hl4 : (-1/10 : ℝ) ≤ x5) (hu4 : x5 ≤ (-1/20 : ℝ)) (hl5 : (-1/10 : ℝ) ≤ x6) (hu5 : x6 ≤ (-3/100 : ℝ)) : (0 : ℝ) ≤ -x1*x4^2 - 1/3*x1 + x2^2*x6 + x3^2*x5 + x4^3 + x4^2 + 4/3*x4 + 36/25 := by
  let t0 : ℝ := (x1 - (-1)) / (1)
  have ht0 : 0 ≤ t0 := by dsimp [t0]; positivity
  have ht0u : t0 ≤ 1 := by dsimp [t0]; apply (div_le_one (by norm_num)).2; linarith
  have htc0 : 0 ≤ 1 - t0 := sub_nonneg.mpr ht0u
  have hv0 : x1 = (-1) + (1) * t0 := by dsimp [t0]; ring
  let t1 : ℝ := (x2 - (-1/10)) / (1)
  have ht1 : 0 ≤ t1 := by dsimp [t1]; positivity
  have ht1u : t1 ≤ 1 := by dsimp [t1]; apply (div_le_one (by norm_num)).2; linarith
  have htc1 : 0 ≤ 1 - t1 := sub_nonneg.mpr ht1u
  have hv1 : x2 = (-1/10) + (1) * t1 := by dsimp [t1]; ring
  let t2 : ℝ := (x3 - (-1/10)) / (3/5)
  have ht2 : 0 ≤ t2 := by dsimp [t2]; positivity
  have ht2u : t2 ≤ 1 := by dsimp [t2]; apply (div_le_one (by norm_num)).2; linarith
  have htc2 : 0 ≤ 1 - t2 := sub_nonneg.mpr ht2u
  have hv2 : x3 = (-1/10) + (3/5) * t2 := by dsimp [t2]; ring
  let t3 : ℝ := (x4 - (-1)) / (9/10)
  have ht3 : 0 ≤ t3 := by dsimp [t3]; positivity
  have ht3u : t3 ≤ 1 := by dsimp [t3]; apply (div_le_one (by norm_num)).2; linarith
  have htc3 : 0 ≤ 1 - t3 := sub_nonneg.mpr ht3u
  have hv3 : x4 = (-1) + (9/10) * t3 := by dsimp [t3]; ring
  let t4 : ℝ := (x5 - (-1/10)) / (1/20)
  have ht4 : 0 ≤ t4 := by dsimp [t4]; positivity
  have ht4u : t4 ≤ 1 := by dsimp [t4]; apply (div_le_one (by norm_num)).2; linarith
  have htc4 : 0 ≤ 1 - t4 := sub_nonneg.mpr ht4u
  have hv4 : x5 = (-1/10) + (1/20) * t4 := by dsimp [t4]; ring
  let t5 : ℝ := (x6 - (-1/10)) / (7/100)
  have ht5 : 0 ≤ t5 := by dsimp [t5]; positivity
  have ht5u : t5 ≤ 1 := by dsimp [t5]; apply (div_le_one (by norm_num)).2; linarith
  have htc5 : 0 ≤ 1 - t5 := sub_nonneg.mpr ht5u
  have hv5 : x6 = (-1/10) + (7/100) * t5 := by dsimp [t5]; ring
  have hid : (-x1*x4^2 - 1/3*x1 + x2^2*x6 + x3^2*x5 + x4^3 + x4^2 + 4/3*x4 + 36/25) = ((1/1500) + (6529276674470254037/15567111662502400000) * (t0*t3) + (3/1300) * (t3*(1 - t4)) + (243601098160519107/486472239453200000) * (t3*(1 - t5)) + (55746706288665773281/46701334987507200000) * ((1 - t0)*(1 - t3)) + (124979890560978769/912135448974750000) * ((1 - t0)*(1 - t5)) + (7/125) * ((1 - t1)*(1 - t5)) + (13659501/569933000) * ((1 - t2)*(1 - t5)) + (124979890560978769/912135448974750000) * (t0*t3*(1 - t0)) + (288/66875) * (t1*(1 - t1)*(1 - t3)) + (49/13000) * (t2*t4*(1 - t4)) + (34757/2849665) * (t2*t5*(1 - t2)) + (411/13000) * (t2*(1 - t2)^2) + (61/910) * (t3*(1 - t2)*(1 - t3)) + (124979890560978769/912135448974750000) * (t5*(1 - t0)*(1 - t5)) + (98149179523/1845158087500) * (t5*(1 - t5)^2) + (7/100) * (t1*t2*(1 - t1)*(1 - t5)) + (7/100) * (t1*(1 - t1)*(1 - t2)*(1 - t5)) + (1/1625) * (t3*(t2 + t4)^2) + (69514/2849665) * (t3*(t2 + t5)^2) + (1/1625) * ((1 - t4)*(t3 + t4)^2) + (69514/2849665) * ((1 - t2)*(t3 + t5)^2) + (194722998021/3690316175000) * ((1 - t3)*(t3 + t5)^2) + (120654337023/1845158087500) * ((1 - t5)*(t3 + t5)^2) + (99874573/569933000) * ((1 - t3)*(t3 - 0)^2) + (3744/66875) * (t3*(t1 - 1/16)^2) + (3347706/71241625) * (t3*(t2 - 1/16)^2) + (3/325) * (t4*(t2 - 1/16)^2) + (1/1625) * (t4*(t3 - 1/16)^2) + (78844333761/461289521875) * (t5*(t3 - 1/16)^2) + (613849823108568731/912135448974750000) * ((1 - t0)*(t3 - 1/16)^2) + (429148/71241625) * ((1 - t2)*(t3 - 1/16)^2) + (1/1625) * (t3*(t4 - 1/16)^2) + (20187923670671441/912135448974750000) * (t3*(t5 - 1/16)^2) + (6231/267500) * ((t1 - 1)^2) + (4032/66875) * (t1*(t1 - 1)^2) + (3531651349771/3690316175000) * (t3*(t3 - 1)^2) + (1/1625) * (t4*(t4 - 1)^2) + (9/250) * ((1 - t2)*(t2 + t3 - 0)^2) + (124979890560978769/912135448974750000) * ((1 - t0)*(t3 + t5 - 0)^2) + (124979890560978769/912135448974750000) * (t3*(t0 + t5 - 1/8)^2) + (3024/66875) * ((1 - t1)*(t1 + t3 - 1/8)^2) + (1/1625) * ((1 - t2)*(t3 + t4 - 1/8)^2) + (57/13000) * (t2*(t2 + t4 - 1)^2) + (34757/2849665) * (t5*(t2 + t5 - 593/400)^2) + (1008/66875) * ((1 - t1)*(1 - t3)*(t1 + t3 - 0)^2) + (1008/66875) * (t3*(1 - t1)*(t1 + t3 - 2)^2)) := by
    rw [hv0, hv1, hv2, hv3, hv4, hv5]
    ring
  rw [hid]
  positivity

end Lean92.BoxPoly45_BoxPoly45_18


set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 18
name: Butcher's Problem
source_status: confirmed_transformed
basis: 1819
paper_title: Formalization of Bernstein Polynomials and Applications to Global Optimization / A Tool for Formal Verification of Nonlinear Inequalities
paper_url: https://doi.org/10.1007/s10817-012-9256-3
source_evidence: paper_examples_extract/bernstein.txt:2333-2337,2351; paper_examples_extract/FormalVerifier.txt:320-321

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_18_butcher_s_problem :
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
        0 <= -x1*x4^2 - (1 / 3 : ℝ)*x1 + x2^2*x6 + x3^2*x5 + x4^3 + x4^2 + (4 / 3 : ℝ)*x4 + (36 / 25 : ℝ) := by
  intro x1 x2 x3 x4 x5 x6 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4, hl5, hu5⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_18.result x1 x2 x3 x4 x5 x6 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num) (by convert hl5 using 1 <;> norm_num) (by convert hu5 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_18_butcher_s_problem
