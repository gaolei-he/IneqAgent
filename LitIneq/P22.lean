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

namespace Lean92.BoxPoly45_BoxPoly45_22

theorem result (x1 x2 x3 : ℝ) (hl0 : (-5 : ℝ) ≤ x1) (hu0 : x1 ≤ (5 : ℝ)) (hl1 : (-5 : ℝ) ≤ x2) (hu1 : x2 ≤ (5 : ℝ)) (hl2 : (-5 : ℝ) ≤ x3) (hu2 : x3 ≤ (5 : ℝ)) : (0 : ℝ) ≤ 917817267/25000000 + x1 + x3 - 582182733/500000000*x2 - 417817267/500000000*x2^2 := by
  let t0 : ℝ := (x1 - (-5)) / (10)
  have ht0 : 0 ≤ t0 := by dsimp [t0]; positivity
  have ht0u : t0 ≤ 1 := by dsimp [t0]; apply (div_le_one (by norm_num)).2; linarith
  have htc0 : 0 ≤ 1 - t0 := sub_nonneg.mpr ht0u
  have hv0 : x1 = (-5) + (10) * t0 := by dsimp [t0]; ring
  let t1 : ℝ := (x2 - (-5)) / (10)
  have ht1 : 0 ≤ t1 := by dsimp [t1]; positivity
  have ht1u : t1 ≤ 1 := by dsimp [t1]; apply (div_le_one (by norm_num)).2; linarith
  have htc1 : 0 ≤ 1 - t1 := sub_nonneg.mpr ht1u
  have hv1 : x2 = (-5) + (10) * t1 := by dsimp [t1]; ring
  let t2 : ℝ := (x3 - (-5)) / (10)
  have ht2 : 0 ≤ t2 := by dsimp [t2]; positivity
  have ht2u : t2 ≤ 1 := by dsimp [t2]; apply (div_le_one (by norm_num)).2; linarith
  have htc2 : 0 ≤ 1 - t2 := sub_nonneg.mpr ht2u
  have hv2 : x3 = (-5) + (10) * t2 := by dsimp [t2]; ring
  have hid : (917817267/25000000 + x1 + x3 - 582182733/500000000*x2 - 417817267/500000000*x2^2) = ((0) + (4694146100107448882023/1103844797210450000000) * ((1 - t0)*(1 - t1)) + (7694743379917130444623/1103844797210450000000) * ((1 - t1)*(1 - t2)) + (2746787022239319989/1379805996513062500) * (t2^2*(1 - t2)) + (25771493137306506862/8623787478206640625) * (t0*(t1 - 1/16)^2) + (3673954925183775362/8623787478206640625) * (t2*(t1 - 1/16)^2) + (6328485365909425264183/68990299825653125000) * ((1 - t1)*(t1 - 1/16)^2) + (709638602443702410627/7458410791962500000) * (t1*(t1 - 1)^2) + (19081124944547542607/5519223986052250000) * ((1 - t0)*(t0 + t2 - 0)^2) + (6809385282378085887/5519223986052250000) * ((1 - t2)*(t0 + t2 - 0)^2) + (1892490999249321183/1379805996513062500) * (t0*(t0 + t1 - 1/8)^2) + (1552655281858729541/689902998256531250) * (t2*(t0 + t1 - 1/8)^2) + (321147893303044191/689902998256531250) * ((1 - t1)*(t0 + t1 - 1/8)^2) + (965425667675466124233/275961199302612500000) * ((1 - t1)*(t0 + t2 - 1/8)^2) + (106629625937390923/275961199302612500) * (t0*(t1 + t2 - 1/8)^2) + (3409329823719296968/4484369488667453125) * (t2*(t1 + t2 - 1/8)^2) + (13235183342078589293/17937477954669812500) * (t2*(t1 + t2 - 7/4)^2) + (814227669458070460067/275961199302612500000) * ((1 - t1)*(t0 + t1 + t2 - 0)^2) + (92089287580402063/44153791888418000) * (t0*(t0 + t1 + t2 - 27/10)^2) + (9528071021502819023/5519223986052250000) * (t2*(t0 + t1 + t2 - 3)^2)) := by
    rw [hv0, hv1, hv2]
    ring
  rw [hid]
  positivity

end Lean92.BoxPoly45_BoxPoly45_22


set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 22
id: A02
name: R.D. 3
source_status: confirmed_transformed
paper_title: An efficient algorithm for range computation of polynomials using the Bernstein form
paper_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: x1 - 2*x2 + x3 + 835634534/1000000000*x2*(1-x2) + 3671269068/100000000
source_evidence: PDF DOI 10.1007/s10898-008-9382-y; Table 1 Ex 2; Appendix A Problem 2

The theorem statement is a direct Lean syntax translation of the JSONL record:
constraints are kept in their listed order, and f is not algebraically transformed.
-/
theorem box_benchmark_22_a02_r_d_3 :
    ∀ x1 x2 x3 : ℝ,
      -5 <= x1 ∧
      x1 <= 5 ∧
      -5 <= x2 ∧
      x2 <= 5 ∧
      -5 <= x3 ∧
      x3 <= 5 →
        0 <= (917817267 / 25000000 : ℝ) + x1 + x3 - (582182733 / 500000000 : ℝ)*x2 - (417817267 / 500000000 : ℝ)*x2^2 := by
  intro x1 x2 x3 ⟨hl0, hu0, hl1, hu1, hl2, hu2⟩
  have htranslated := @Lean92.BoxPoly45_BoxPoly45_22.result x1 x2 x3 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources

#print axioms Leanpro.BoxJsonlWithSources.box_benchmark_22_a02_r_d_3
