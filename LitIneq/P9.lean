import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 x4 x5 x6 : ℝ) (hl0 : (-100 : ℝ) ≤ x1) (hu0 : x1 ≤ (100 : ℝ)) (hl1 : (-100 : ℝ) ≤ x2) (hu1 : x2 ≤ (100 : ℝ)) (hl2 : (-100 : ℝ) ≤ x3) (hu2 : x3 ≤ (100 : ℝ)) (hl3 : (-100 : ℝ) ≤ x4) (hu3 : x4 ≤ (100 : ℝ)) (hl4 : (-100 : ℝ) ≤ x5) (hu4 : x5 ≤ (100 : ℝ)) (hl5 : (-100 : ℝ) ≤ x6) (hu5 : x6 ≤ (100 : ℝ)) : (0 : ℝ) ≤ -34/5*x1*x4 - 16/5*x1*x5 + 13/10*x1*x6 + 51/10*x1 - 24/5*x2*x5 - 7/10*x2*x6 - 71/10*x2 - 19/10*x3*x4 - 7/10*x3*x5 + 9*x3*x6 - x3 + 51/10*x4 - 71/10*x5 - x6 + 270400 := by
  let t0 : ℝ := (x1 - (-100)) / (200)
  have ht0 : 0 ≤ t0 := by dsimp [t0]; positivity
  have ht0u : t0 ≤ 1 := by dsimp [t0]; apply (div_le_one (by norm_num)).2; linarith
  have htc0 : 0 ≤ 1 - t0 := sub_nonneg.mpr ht0u
  have hv0 : x1 = (-100) + (200) * t0 := by dsimp [t0]; ring
  let t1 : ℝ := (x2 - (-100)) / (200)
  have ht1 : 0 ≤ t1 := by dsimp [t1]; positivity
  have ht1u : t1 ≤ 1 := by dsimp [t1]; apply (div_le_one (by norm_num)).2; linarith
  have htc1 : 0 ≤ 1 - t1 := sub_nonneg.mpr ht1u
  have hv1 : x2 = (-100) + (200) * t1 := by dsimp [t1]; ring
  let t2 : ℝ := (x3 - (-100)) / (200)
  have ht2 : 0 ≤ t2 := by dsimp [t2]; positivity
  have ht2u : t2 ≤ 1 := by dsimp [t2]; apply (div_le_one (by norm_num)).2; linarith
  have htc2 : 0 ≤ 1 - t2 := sub_nonneg.mpr ht2u
  have hv2 : x3 = (-100) + (200) * t2 := by dsimp [t2]; ring
  let t3 : ℝ := (x4 - (-100)) / (200)
  have ht3 : 0 ≤ t3 := by dsimp [t3]; positivity
  have ht3u : t3 ≤ 1 := by dsimp [t3]; apply (div_le_one (by norm_num)).2; linarith
  have htc3 : 0 ≤ 1 - t3 := sub_nonneg.mpr ht3u
  have hv3 : x4 = (-100) + (200) * t3 := by dsimp [t3]; ring
  let t4 : ℝ := (x5 - (-100)) / (200)
  have ht4 : 0 ≤ t4 := by dsimp [t4]; positivity
  have ht4u : t4 ≤ 1 := by dsimp [t4]; apply (div_le_one (by norm_num)).2; linarith
  have htc4 : 0 ≤ 1 - t4 := sub_nonneg.mpr ht4u
  have hv4 : x5 = (-100) + (200) * t4 := by dsimp [t4]; ring
  let t5 : ℝ := (x6 - (-100)) / (200)
  have ht5 : 0 ≤ t5 := by dsimp [t5]; positivity
  have ht5u : t5 ≤ 1 := by dsimp [t5]; apply (div_le_one (by norm_num)).2; linarith
  have htc5 : 0 ≤ 1 - t5 := sub_nonneg.mpr ht5u
  have hv5 : x6 = (-100) + (200) * t5 := by dsimp [t5]; ring
  have hid : (-34/5*x1*x4 - 16/5*x1*x5 + 13/10*x1*x6 + 51/10*x1 - 24/5*x2*x5 - 7/10*x2*x6 - 71/10*x2 - 19/10*x3*x4 - 7/10*x3*x5 + 9*x3*x6 - x3 + 51/10*x4 - 71/10*x5 - x6 + 270400) = ((0) + (45577460/689) * (t0*(1 - t4)) + (80580) * (t1*(1 - t4)) + (115072700/689) * (t2*t5) + (44637500/689) * (t2*(1 - t3)) + (7726500/689) * (t3*(1 - t2)) + (23322540/689) * (t4*(1 - t0)) + (83420) * (t4*(1 - t1)) + (28000) * (t4*(1 - t2)) + (132967300/689) * ((1 - t2)*(1 - t5)) + (74545720/689) * (t0*t1*(1 - t3)) + (19430400/689) * (t0*t5*(1 - t0)) + (17584800/689) * (t0*t5*(1 - t4)) + (620800/689) * (t0*(1 - t0)*(1 - t4)) + (74545720/689) * (t0*(1 - t1)*(1 - t3)) + (28000) * (t1*(1 - t4)*(1 - t5)) + (112862280/689) * (t2*t3*(1 - t0)) + (112862280/689) * (t3*(1 - t0)*(1 - t2)) + (28000) * (t4*t5*(1 - t1)) + (18826400/689) * (t4*(1 - t0)*(1 - t5)) + (620800/689) * (t5*(1 - t4)*(1 - t5)) + (19430400/689) * (t5*(t0 - 1/16)^2) + (620800/689) * ((1 - t4)*(t0 + t5 - 1/8)^2)) := by
    rw [hv0, hv1, hv2, hv3, hv4, hv5]
    ring
  rw [hid]
  positivity



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 9
name: C10
reference: A general solver based on sparse resultants: Numerical issues and kinematic applications

-/
theorem box_benchmark_09_c10 :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      -100 <= x1 ∧
      x1 <= 100 ∧
      -100 <= x2 ∧
      x2 <= 100 ∧
      -100 <= x3 ∧
      x3 <= 100 ∧
      -100 <= x4 ∧
      x4 <= 100 ∧
      -100 <= x5 ∧
      x5 <= 100 ∧
      -100 <= x6 ∧
      x6 <= 100 →
        0 <= (-34 / 5 : ℝ)*x1*x4 - (16 / 5 : ℝ)*x1*x5 + (13 / 10 : ℝ)*x1*x6 + (51 / 10 : ℝ)*x1 - (24 / 5 : ℝ)*x2*x5 - (7 / 10 : ℝ)*x2*x6 - (71 / 10 : ℝ)*x2 - (19 / 10 : ℝ)*x3*x4 - (7 / 10 : ℝ)*x3*x5 + 9*x3*x6 - x3 + (51 / 10 : ℝ)*x4 - (71 / 10 : ℝ)*x5 - x6 + 270400 := by
  intro x1 x2 x3 x4 x5 x6 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4, hl5, hu5⟩
  have htranslated := @result x1 x2 x3 x4 x5 x6 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num) (by convert hl5 using 1 <;> norm_num) (by convert hu5 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
