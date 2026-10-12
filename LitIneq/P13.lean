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

namespace Lean92.BoxPoly45_BoxPoly45_13

theorem result (x1 x2 x3 x4 : ℝ) (hl0 : (-2 : ℝ) ≤ x1) (hu0 : x1 ≤ (2 : ℝ)) (hl1 : (-2 : ℝ) ≤ x2) (hu1 : x2 ≤ (2 : ℝ)) (hl2 : (-2 : ℝ) ≤ x3) (hu2 : x3 ≤ (2 : ℝ)) (hl3 : (-2 : ℝ) ≤ x4) (hu3 : x4 ≤ (2 : ℝ)) : (0 : ℝ) ≤ x1*x2^2 + x1*x3^2 + x1*x4^2 - 11/10*x1 + 109/5 := by
  let t0 : ℝ := (x1 - (-2)) / (4)
  have ht0 : 0 ≤ t0 := by dsimp [t0]; positivity
  have ht0u : t0 ≤ 1 := by dsimp [t0]; apply (div_le_one (by norm_num)).2; linarith
  have htc0 : 0 ≤ 1 - t0 := sub_nonneg.mpr ht0u
  have hv0 : x1 = (-2) + (4) * t0 := by dsimp [t0]; ring
  let t1 : ℝ := (x2 - (-2)) / (4)
  have ht1 : 0 ≤ t1 := by dsimp [t1]; positivity
  have ht1u : t1 ≤ 1 := by dsimp [t1]; apply (div_le_one (by norm_num)).2; linarith
  have htc1 : 0 ≤ 1 - t1 := sub_nonneg.mpr ht1u
  have hv1 : x2 = (-2) + (4) * t1 := by dsimp [t1]; ring
  let t2 : ℝ := (x3 - (-2)) / (4)
  have ht2 : 0 ≤ t2 := by dsimp [t2]; positivity
  have ht2u : t2 ≤ 1 := by dsimp [t2]; apply (div_le_one (by norm_num)).2; linarith
  have htc2 : 0 ≤ 1 - t2 := sub_nonneg.mpr ht2u
  have hv2 : x3 = (-2) + (4) * t2 := by dsimp [t2]; ring
  let t3 : ℝ := (x4 - (-2)) / (4)
  have ht3 : 0 ≤ t3 := by dsimp [t3]; positivity
  have ht3u : t3 ≤ 1 := by dsimp [t3]; apply (div_le_one (by norm_num)).2; linarith
  have htc3 : 0 ≤ 1 - t3 := sub_nonneg.mpr ht3u
  have hv3 : x4 = (-2) + (4) * t3 := by dsimp [t3]; ring
  have hid : (x1*x2^2 + x1*x3^2 + x1*x4^2 - 11/10*x1 + 109/5) = ((0) + (544/49) * (t0^2*t1^2) + (544/49) * (t0^2*t2^2) + (4384/245) * (t0^2*t3*(1 - t3)) + (32) * (t1*(1 - t0)^2*(1 - t1)) + (32) * (t2*(1 - t0)^2*(1 - t2)) + (32) * (t3*(1 - t0)^2*(1 - t3)) + (1024/49) * ((1 - t0)*(t0*t1 - 0)^2) + (1024/49) * ((1 - t0)*(t0*t2 - 0)^2) + (207808/12005) * ((t0*t3 - 0)^2) + (391168/12005) * ((1 - t0)*(t0*t3 - 0)^2) + (1024/49) * (t0*(t0*t1 - 49/64)^2) + (1024/49) * (t0*(t0*t2 - 49/64)^2) + (391168/12005) * (t0*(t0*t3 - 49/64)^2)) := by
    rw [hv0, hv1, hv2, hv3]
    ring
  rw [hid]
  positivity

end Lean92.BoxPoly45_BoxPoly45_13


set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 13
name: C5
source_status: confirmed_from_appirl_citation_and_code
basis: 494
paper_title: The PHC Pack, the database of polynomial systems
source_evidence: /home/ljh/APPIRL/proof/Example.py:59-63; /tmp/2503.06592v1.layout.txt:521-530; /tmp/2503.06592v1.layout.txt:537; /tmp/2503.06592v1.layout.txt:753-754

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_13_c5 :
    ∀ x1 x2 x3 x4 : ℝ,
      -2 <= x1 ∧
      x1 <= 2 ∧
      -2 <= x2 ∧
      x2 <= 2 ∧
      -2 <= x3 ∧
      x3 <= 2 ∧
      -2 <= x4 ∧
      x4 <= 2 →
        0 <= x1*x2^2 + x1*x3^2 + x1*x4^2 - (11 / 10 : ℝ)*x1 + (109 / 5 : ℝ) := by
  intro x1 x2 x3 x4 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_13.result x1 x2 x3 x4 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_13_c5
