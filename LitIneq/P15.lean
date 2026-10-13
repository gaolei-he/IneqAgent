import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 x4 : ℝ) (hl0 : (-1/2 : ℝ) ≤ x1) (hu0 : x1 ≤ (1/2 : ℝ)) (hl1 : (-1/2 : ℝ) ≤ x2) (hu1 : x2 ≤ (1/2 : ℝ)) (hl2 : (-1/2 : ℝ) ≤ x3) (hu2 : x3 ≤ (1/2 : ℝ)) (hl3 : (-1/2 : ℝ) ≤ x4) (hu3 : x4 ≤ (1/2 : ℝ)) : (0 : ℝ) ≤ -x1*x3^3 + 4*x1*x3*x4^2 + 4*x1*x3 + 4*x2*x3^2*x4 + 2*x2*x4^3 - 10*x2*x4 + 4*x3^2 - 10*x4^2 + 51801/10000 := by
  let t0 : ℝ := (x1 - (-1/2)) / (1)
  have ht0 : 0 ≤ t0 := by dsimp [t0]; positivity
  have ht0u : t0 ≤ 1 := by dsimp [t0]; apply (div_le_one (by norm_num)).2; linarith
  have htc0 : 0 ≤ 1 - t0 := sub_nonneg.mpr ht0u
  have hv0 : x1 = (-1/2) + (1) * t0 := by dsimp [t0]; ring
  let t1 : ℝ := (x2 - (-1/2)) / (1)
  have ht1 : 0 ≤ t1 := by dsimp [t1]; positivity
  have ht1u : t1 ≤ 1 := by dsimp [t1]; apply (div_le_one (by norm_num)).2; linarith
  have htc1 : 0 ≤ 1 - t1 := sub_nonneg.mpr ht1u
  have hv1 : x2 = (-1/2) + (1) * t1 := by dsimp [t1]; ring
  let t2 : ℝ := (x3 - (-1/2)) / (1)
  have ht2 : 0 ≤ t2 := by dsimp [t2]; positivity
  have ht2u : t2 ≤ 1 := by dsimp [t2]; apply (div_le_one (by norm_num)).2; linarith
  have htc2 : 0 ≤ 1 - t2 := sub_nonneg.mpr ht2u
  have hv2 : x3 = (-1/2) + (1) * t2 := by dsimp [t2]; ring
  let t3 : ℝ := (x4 - (-1/2)) / (1)
  have ht3 : 0 ≤ t3 := by dsimp [t3]; positivity
  have ht3u : t3 ≤ 1 := by dsimp [t3]; apply (div_le_one (by norm_num)).2; linarith
  have htc3 : 0 ≤ 1 - t3 := sub_nonneg.mpr ht3u
  have hv3 : x4 = (-1/2) + (1) * t3 := by dsimp [t3]; ring
  have hid : (-x1*x3^3 + 4*x1*x3*x4^2 + 4*x1*x3 + 4*x2*x3^2*x4 + 2*x2*x4^3 - 10*x2*x4 + 4*x3^2 - 10*x4^2 + 51801/10000) = ((1361/538880000) + (431/90) * (t0^2*t3*(1 - t3)) + (431/45) * (t0*t3*(1 - t0)*(1 - t3)) + (4) * (t2*t3*(1 - t2)*(1 - t3)) + (431/90) * (t3*(1 - t0)^2*(1 - t3)) + (2) * (t0*t3*(1 - t2)^2*(1 - t3)) + (164/45) * (t1^3*t3*(1 - t3)) + (1/2) * (t1^3*(1 - t3)^2) + (259/60) * (t1^2*t3^2*(1 - t3)) + (2) * (t1*t2*(1 - t2)*(1 - t3)^2) + (17/30) * (t1*t3*(1 - t1)^2*(1 - t3)) + (1/2) * (t1*(1 - t1)^2*(1 - t3)^2) + (2) * (t2^2*t3*(1 - t0)*(1 - t3)) + (2) * (t2*t3^2*(1 - t1)*(1 - t2)) + (289/90) * (t3*(1 - t1)^3*(1 - t3)) + (15/4) * ((1 - t1)*(t1*t3 - 0)^2) + (15/4) * (t1*(t1*t3 - 1)^2) + (3823/900) * (t3*(t1*t3 - 1)^2) + (253/5894) * (t0*t2*(t2 - 1/4)^2) + (29161/5894) * (t0*t3*(t2 - 207/800)^2) + (1600/2947) * (t0*(1 - t2)*(t2 - 207/800)^2) + (29161/5894) * (t0*(1 - t3)*(t2 - 207/800)^2) + (29161/5894) * ((1 - t0)*(t2 - 593/800)^2) + (1600/2947) * (t2*(1 - t0)*(t2 - 593/800)^2) + (253/5894) * ((1 - t0)*(1 - t2)*(t2 - 3/4)^2) + (1) * ((1 - t1)*(1 - t3)*(t1 + t3 - 0)^2) + (1/2) * ((1 - t3)^2*(t1*t3 - 0)^2) + (128/225) * (t3*(1 - t1)*(t1*t3 - 1/16)^2) + (128/225) * (t1*t3*(t1*t3 - 1)^2) + (1/2) * (t3*(1 - t3)*(t1*t3 - 1)^2)) := by
    rw [hv0, hv1, hv2, hv3]
    ring
  rw [hid]
  positivity



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 15
name: Caprasse's System
reference: Formalization of Bernstein Polynomials and Applications to Global Optimization / A Tool for Formal Verification of Nonlinear Inequalities
reference_url: https://doi.org/10.1007/s10817-012-9256-3

-/
theorem box_benchmark_15_caprasse_s_system :
    ∀ x1 x2 x3 x4 : ℝ,
      (-1 / 2 : ℝ) <= x1 ∧
      x1 <= (1 / 2 : ℝ) ∧
      (-1 / 2 : ℝ) <= x2 ∧
      x2 <= (1 / 2 : ℝ) ∧
      (-1 / 2 : ℝ) <= x3 ∧
      x3 <= (1 / 2 : ℝ) ∧
      (-1 / 2 : ℝ) <= x4 ∧
      x4 <= (1 / 2 : ℝ) →
        0 <= -x1*x3^3 + 4*x1*x3*x4^2 + 4*x1*x3 + 4*x2*x3^2*x4 + 2*x2*x4^3 - 10*x2*x4 + 4*x3^2 - 10*x4^2 + (51801 / 10000 : ℝ) := by
  intro x1 x2 x3 x4 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3⟩
  have htranslated := @result x1 x2 x3 x4 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
