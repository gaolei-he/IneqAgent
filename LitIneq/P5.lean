import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 : ℝ) (hl0 : (-5 : ℝ) ≤ x1) (hu0 : x1 ≤ (5 : ℝ)) (hl1 : (-5 : ℝ) ≤ x2) (hu1 : x2 ≤ (5 : ℝ)) (hl2 : (-5 : ℝ) ≤ x3) (hu2 : x3 ≤ (5 : ℝ)) : (0 : ℝ) ≤ -x1 + 417817267/500000000*x2^2 + 582182733/500000000*x2 - x3 + 4726057557/250000000 := by
  have hcert : (0 : ℝ) ≤ ((-1)*(x1)) + ((417817267/500000000)*((x2)^2)) + ((582182733/500000000)*(x2)) + ((-1)*(x3)) + (4726057557/250000000) := by
    have hgg1 : (0 : ℝ) ≤ (x1) + (5) := by first | positivity | nlinarith
    have hsg1 : (0 : ℝ) ≤ (10/49)*(1)^2 := by positivity
    have hpg1 := mul_nonneg hsg1 hgg1
    have hgg2 : (0 : ℝ) ≤ (5) + ((-1)*(x1)) := by first | positivity | nlinarith
    have hsg2 : (0 : ℝ) ≤ (59/49)*(1)^2 := by positivity
    have hpg2 := mul_nonneg hsg2 hgg2
    have hgg3 : (0 : ℝ) ≤ (x2) + (5) := by first | positivity | nlinarith
    have hsg3 : (0 : ℝ) ≤ (4/7)*(1)^2 := by positivity
    have hpg3 := mul_nonneg hsg3 hgg3
    have hgg4 : (0 : ℝ) ≤ (5) + ((-1)*(x2)) := by first | positivity | nlinarith
    have hsg4 : (0 : ℝ) ≤ (13/49)*(1)^2 := by positivity
    have hpg4 := mul_nonneg hsg4 hgg4
    have hgg5 : (0 : ℝ) ≤ (x3) + (5) := by first | positivity | nlinarith
    have hsg5 : (0 : ℝ) ≤ (10/49)*(1)^2 := by positivity
    have hpg5 := mul_nonneg hsg5 hgg5
    have hgg6 : (0 : ℝ) ≤ (5) + ((-1)*(x3)) := by first | positivity | nlinarith
    have hsg6 : (0 : ℝ) ≤ (59/49)*(1)^2 := by positivity
    have hpg6 := mul_nonneg hsg6 hgg6
    have hs0 : (0 : ℝ) ≤ (12250000000/7826820293)*((7826820293/12250000000) + (21026953917/49000000000)*x2)^2 + (1534056777428000000000/839778029307946855663)*((839778029307946855663/1534056777428000000000)*x2)^2 := by positivity
    have hid : (((-1)*(x1)) + ((417817267/500000000)*((x2)^2)) + ((582182733/500000000)*(x2)) + ((-1)*(x3)) + (4726057557/250000000)) = (((12250000000/7826820293)*((7826820293/12250000000) + (21026953917/49000000000)*x2)^2 + (1534056777428000000000/839778029307946855663)*((839778029307946855663/1534056777428000000000)*x2)^2) + ((10/49)*(1)^2)*((x1) + (5)) + ((59/49)*(1)^2)*((5) + ((-1)*(x1))) + ((4/7)*(1)^2)*((x2) + (5)) + ((13/49)*(1)^2)*((5) + ((-1)*(x2))) + ((10/49)*(1)^2)*((x3) + (5)) + ((59/49)*(1)^2)*((5) + ((-1)*(x3)))) := by ring
    rw [hid]
    linarith
  convert hcert using 1 <;> ring



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 5
name: C3
reference: Personal communication at the occasion of the AMS-SIAM summer seminar in applied mathematics

-/
theorem box_benchmark_05_c3 :
    ∀ x1 x2 x3 : ℝ,
      -5 <= x1 ∧
      x1 <= 5 ∧
      -5 <= x2 ∧
      x2 <= 5 ∧
      -5 <= x3 ∧
      x3 <= 5 →
        0 <= -x1 + (417817267 / 500000000 : ℝ)*x2^2 + (582182733 / 500000000 : ℝ)*x2 - x3 + (4726057557 / 250000000 : ℝ) := by
  intro x1 x2 x3 ⟨hl0, hu0, hl1, hu1, hl2, hu2⟩
  have htranslated := @result x1 x2 x3 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
