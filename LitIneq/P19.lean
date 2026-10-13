import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 x4 x5 : ℝ) (hl0 : (-10 : ℝ) ≤ x1) (hu0 : x1 ≤ (10 : ℝ)) (hl1 : (-10 : ℝ) ≤ x2) (hu1 : x2 ≤ (10 : ℝ)) (hl2 : (-10 : ℝ) ≤ x3) (hu2 : x3 ≤ (10 : ℝ)) (hl3 : (-10 : ℝ) ≤ x4) (hu3 : x4 ≤ (10 : ℝ)) (hl4 : (-10 : ℝ) ≤ x5) (hu4 : x5 ≤ (10 : ℝ)) : (0 : ℝ) ≤ x1*x2*x3*x4 + x1*x2*x3*x5 + x1*x2*x4*x5 + x1*x3*x4*x5 + x2*x3*x4*x5 + 30000 := by
  let t0 : ℝ := (x1 - (-10)) / (20)
  have ht0 : 0 ≤ t0 := by dsimp [t0]; positivity
  have ht0u : t0 ≤ 1 := by dsimp [t0]; apply (div_le_one (by norm_num)).2; linarith
  have htc0 : 0 ≤ 1 - t0 := sub_nonneg.mpr ht0u
  have hv0 : x1 = (-10) + (20) * t0 := by dsimp [t0]; ring
  let t1 : ℝ := (x2 - (-10)) / (20)
  have ht1 : 0 ≤ t1 := by dsimp [t1]; positivity
  have ht1u : t1 ≤ 1 := by dsimp [t1]; apply (div_le_one (by norm_num)).2; linarith
  have htc1 : 0 ≤ 1 - t1 := sub_nonneg.mpr ht1u
  have hv1 : x2 = (-10) + (20) * t1 := by dsimp [t1]; ring
  let t2 : ℝ := (x3 - (-10)) / (20)
  have ht2 : 0 ≤ t2 := by dsimp [t2]; positivity
  have ht2u : t2 ≤ 1 := by dsimp [t2]; apply (div_le_one (by norm_num)).2; linarith
  have htc2 : 0 ≤ 1 - t2 := sub_nonneg.mpr ht2u
  have hv2 : x3 = (-10) + (20) * t2 := by dsimp [t2]; ring
  let t3 : ℝ := (x4 - (-10)) / (20)
  have ht3 : 0 ≤ t3 := by dsimp [t3]; positivity
  have ht3u : t3 ≤ 1 := by dsimp [t3]; apply (div_le_one (by norm_num)).2; linarith
  have htc3 : 0 ≤ 1 - t3 := sub_nonneg.mpr ht3u
  have hv3 : x4 = (-10) + (20) * t3 := by dsimp [t3]; ring
  let t4 : ℝ := (x5 - (-10)) / (20)
  have ht4 : 0 ≤ t4 := by dsimp [t4]; positivity
  have ht4u : t4 ≤ 1 := by dsimp [t4]; apply (div_le_one (by norm_num)).2; linarith
  have htc4 : 0 ≤ 1 - t4 := sub_nonneg.mpr ht4u
  have hv4 : x5 = (-10) + (20) * t4 := by dsimp [t4]; ring
  have hid : (x1*x2*x3*x4 + x1*x2*x3*x5 + x1*x2*x4*x5 + x1*x3*x4*x5 + x2*x3*x4*x5 + 30000) = ((0) + (24000) * (t0*t1*(1 - t2)*(1 - t4)) + (12000) * (t0*t2*(1 - t0)*(1 - t2)) + (8000) * (t0*t2*(1 - t3)*(1 - t4)) + (24000) * (t0*t4*(1 - t2)*(1 - t3)) + (24000) * (t1*t2*(1 - t1)*(1 - t2)) + (24000) * (t1*t3*(1 - t0)*(1 - t4)) + (4000) * (t1*t3*(1 - t1)*(1 - t3)) + (20000) * (t1*t4*(1 - t1)*(1 - t4)) + (4000) * (t2*t3*(1 - t2)*(1 - t3)) + (24000) * (t2*t4*(1 - t0)*(1 - t1)) + (8000) * (t3*t4*(1 - t0)*(1 - t1)) + (12000) * (t0^2*t2*(1 - t1)*(1 - t2)) + (16000) * (t0*t1^2*(1 - t3)*(1 - t4)) + (80000) * (t0*t1*t2*t3*t4) + (8000) * (t0*t1*t4*(1 - t1)*(1 - t4)) + (16000) * (t0*t1*(1 - t1)*(1 - t4)^2) + (16000) * (t0*t2^2*(1 - t1)*(1 - t3)) + (8000) * (t0*t2*t4*(1 - t0)*(1 - t2)) + (16000) * (t0*t2*(1 - t1)^2*(1 - t4)) + (4000) * (t0*t2*(1 - t2)*(1 - t3)^2) + (8000) * (t0*t3*(1 - t1)^2*(1 - t2)) + (8000) * (t0*t3*(1 - t1)^2*(1 - t4)) + (24000) * (t0*t3*(1 - t1)*(1 - t2)^2) + (16000) * (t0*t4*(1 - t1)^2*(1 - t3)) + (16000) * (t1^2*t2*(1 - t0)*(1 - t3)) + (12000) * (t1^2*t2*(1 - t2)*(1 - t3)) + (16000) * (t1^2*t3*(1 - t2)*(1 - t4)) + (16000) * (t1^2*t4*(1 - t0)*(1 - t2)) + (8000) * (t1^2*t4*(1 - t0)*(1 - t3)) + (8000) * (t1*t2^2*(1 - t0)*(1 - t3)) + (12000) * (t1*t2^2*(1 - t1)*(1 - t4)) + (16000) * (t1*t2^2*(1 - t3)*(1 - t4)) + (12000) * (t1*t2*(1 - t0)^2*(1 - t2)) + (4000) * (t1*t2*(1 - t1)*(1 - t3)^2) + (4000) * (t1*t3^2*(1 - t1)*(1 - t2)) + (12000) * (t1*t3*(1 - t1)*(1 - t4)^2) + (8000) * (t1*t4^2*(1 - t0)*(1 - t1)) + (12000) * (t1*t4^2*(1 - t1)*(1 - t3)) + (4000) * (t1*t4*(1 - t1)*(1 - t2)^2) + (16000) * (t1*t4*(1 - t2)^2*(1 - t3)) + (16000) * (t2^2*t3*(1 - t0)*(1 - t4)) + (8000) * (t2^2*t4*(1 - t0)*(1 - t3)) + (8000) * (t2^2*t4*(1 - t1)*(1 - t3)) + (4000) * (t2*t3^2*(1 - t0)*(1 - t2)) + (8000) * (t2*t3*(1 - t0)*(1 - t1)^2) + (12000) * (t2*t3*(1 - t1)^2*(1 - t2)) + (16000) * (t2*t3*(1 - t1)^2*(1 - t4)) + (8000) * (t2*t4*(1 - t0)^2*(1 - t2)) + (8000) * (t2*t4*(1 - t1)^2*(1 - t2)) + (24000) * (t3*t4*(1 - t0)*(1 - t2)^2) + (8000) * (t3*t4*(1 - t1)*(1 - t2)^2) + (80000) * ((1 - t0)*(1 - t1)*(1 - t2)*(1 - t3)*(1 - t4))) := by
    rw [hv0, hv1, hv2, hv3, hv4]
    ring
  rw [hid]
  positivity



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 19
name: C9
reference: Sparse elimination and applications in kinematics

-/
theorem box_benchmark_19_c9 :
    ∀ x1 x2 x3 x4 x5 : ℝ,
      -10 <= x1 ∧
      x1 <= 10 ∧
      -10 <= x2 ∧
      x2 <= 10 ∧
      -10 <= x3 ∧
      x3 <= 10 ∧
      -10 <= x4 ∧
      x4 <= 10 ∧
      -10 <= x5 ∧
      x5 <= 10 →
        0 <= x1*x2*x3*x4 + x1*x2*x3*x5 + x1*x2*x4*x5 + x1*x3*x4*x5 + x2*x3*x4*x5 + 30000 := by
  intro x1 x2 x3 x4 x5 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4⟩
  have htranslated := @result x1 x2 x3 x4 x5 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
