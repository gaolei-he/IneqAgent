import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 x4 : ℝ) (hl0 : (-5 : ℝ) ≤ x1) (hu0 : x1 ≤ (5 : ℝ)) (hl1 : (-5 : ℝ) ≤ x2) (hu1 : x2 ≤ (5 : ℝ)) (hl2 : (-5 : ℝ) ≤ x3) (hu2 : x3 ≤ (5 : ℝ)) (hl3 : (-5 : ℝ) ≤ x4) (hu3 : x4 ≤ (5 : ℝ)) : (0 : ℝ) ≤ x1*x3^3 - 4*x1*x3*x4^2 - 4*x1*x3 - 4*x2*x3^2*x4 - 2*x2*x4^3 + 10*x2*x4 - 4*x3^2 + 10*x4^2 + 5325 := by
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
  let t3 : ℝ := (x4 - (-5)) / (10)
  have ht3 : 0 ≤ t3 := by dsimp [t3]; positivity
  have ht3u : t3 ≤ 1 := by dsimp [t3]; apply (div_le_one (by norm_num)).2; linarith
  have htc3 : 0 ≤ 1 - t3 := sub_nonneg.mpr ht3u
  have hv3 : x4 = (-5) + (10) * t3 := by dsimp [t3]; ring
  have hid : (x1*x3^3 - 4*x1*x3*x4^2 - 4*x1*x3 - 4*x2*x3^2*x4 - 2*x2*x4^3 + 10*x2*x4 - 4*x3^2 + 10*x4^2 + 5325) = ((0) + (5000) * (t0*t2*(1 - t0)*(1 - t2)) + (7900) * (t0*t3*(1 - t0)*(1 - t3)) + (1450/3) * (t1*t2*(1 - t1)*(1 - t2)) + (125) * (t1*t3*(1 - t1)*(1 - t3)) + (1450/3) * (t2*(1 - t1)^2*(1 - t2)) + (7900) * (t0^2*t2*t3*(1 - t3)) + (5000) * (t0^2*t2*(1 - t2)^2) + (4200) * (t0*t2^2*t3*(1 - t3)) + (3950) * (t0*t3^2*(1 - t2)^2) + (3950) * (t0*(1 - t2)^2*(1 - t3)^2) + (8900) * (t1^2*t3^2*(1 - t3)) + (1100) * (t1^2*(1 - t3)^3) + (4075) * (t1*t2^2*(1 - t3)^2) + (11850) * (t1*t2*t3^2*(1 - t2)) + (2575/3) * (t1*t3^3*(1 - t1)) + (1100) * (t1*t3*(1 - t1)^2*(1 - t3)) + (1450/3) * (t1*t3*(1 - t1)*(1 - t2)^2) + (725/3) * (t1*t3*(1 - t1)*(1 - t3)^2) + (1100) * (t1*(1 - t1)^2*(1 - t3)^2) + (4075) * (t1*(1 - t2)^2*(1 - t3)^2) + (3950) * (t2^2*t3^2*(1 - t0)) + (12950/3) * (t2^2*t3^2*(1 - t1)) + (1450/3) * (t2^2*t3*(1 - t1)*(1 - t3)) + (5000) * (t2^2*(1 - t0)^2*(1 - t2)) + (3950) * (t2^2*(1 - t0)*(1 - t3)^2) + (34100/3) * (t2*(1 - t1)*(1 - t2)*(1 - t3)^2) + (8050/3) * (t3^3*(1 - t1)^2) + (11500/3) * (t3^2*(1 - t1)*(1 - t2)^2) + (7900) * (t3*(1 - t0)^2*(1 - t2)*(1 - t3)) + (4200) * (t3*(1 - t0)*(1 - t2)^2*(1 - t3)) + (1450/3) * (t3*(1 - t1)^2*(1 - t2)^2) + (25250/3) * (t3*(1 - t1)^2*(1 - t3)^2) + (1825) * ((1 - t1)*(t1*t3 - 0)^2) + (1825) * (t1*(t1*t3 - 1)^2) + (1100) * ((1 - t1)*(1 - t3)*(t1 + t3 - 0)^2)) := by
    rw [hv0, hv1, hv2, hv3]
    ring
  rw [hid]
  positivity



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 16
name: C7
reference: A new efficient algorithm for computing Groebner bases (F4)

-/
theorem box_benchmark_16_c7 :
    ∀ x1 x2 x3 x4 : ℝ,
      -5 <= x1 ∧
      x1 <= 5 ∧
      -5 <= x2 ∧
      x2 <= 5 ∧
      -5 <= x3 ∧
      x3 <= 5 ∧
      -5 <= x4 ∧
      x4 <= 5 →
        0 <= x1*x3^3 - 4*x1*x3*x4^2 - 4*x1*x3 - 4*x2*x3^2*x4 - 2*x2*x4^3 + 10*x2*x4 - 4*x3^2 + 10*x4^2 + 5325 := by
  intro x1 x2 x3 x4 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3⟩
  have htranslated := @result x1 x2 x3 x4 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
