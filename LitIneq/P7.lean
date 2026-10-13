import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 : ℝ) (hl0 : (-3/2 : ℝ) ≤ x1) (hu0 : x1 ≤ (2 : ℝ)) (hl1 : (-3/2 : ℝ) ≤ x2) (hu1 : x2 ≤ (2 : ℝ)) (hl2 : (-3/2 : ℝ) ≤ x3) (hu2 : x3 ≤ (2 : ℝ)) : (0 : ℝ) ≤ x1*x2^2 + x1*x3^2 - 11/10*x1 + 207/20 := by
  let t0 : ℝ := (x1 - (-3/2)) / (7/2)
  have ht0 : 0 ≤ t0 := by dsimp [t0]; positivity
  have ht0u : t0 ≤ 1 := by dsimp [t0]; apply (div_le_one (by norm_num)).2; linarith
  have htc0 : 0 ≤ 1 - t0 := sub_nonneg.mpr ht0u
  have hv0 : x1 = (-3/2) + (7/2) * t0 := by dsimp [t0]; ring
  let t1 : ℝ := (x2 - (-3/2)) / (7/2)
  have ht1 : 0 ≤ t1 := by dsimp [t1]; positivity
  have ht1u : t1 ≤ 1 := by dsimp [t1]; apply (div_le_one (by norm_num)).2; linarith
  have htc1 : 0 ≤ 1 - t1 := sub_nonneg.mpr ht1u
  have hv1 : x2 = (-3/2) + (7/2) * t1 := by dsimp [t1]; ring
  let t2 : ℝ := (x3 - (-3/2)) / (7/2)
  have ht2 : 0 ≤ t2 := by dsimp [t2]; positivity
  have ht2u : t2 ≤ 1 := by dsimp [t2]; apply (div_le_one (by norm_num)).2; linarith
  have htc2 : 0 ≤ 1 - t2 := sub_nonneg.mpr ht2u
  have hv2 : x3 = (-3/2) + (7/2) * t2 := by dsimp [t2]; ring
  have hid : (x1*x2^2 + x1*x3^2 - 11/10*x1 + 207/20) = ((0) + (983918/159651) * (t0*t1^2*(1 - t0)) + (3887227/638604) * (t0*t2^2*(1 - t0)) + (4396776750097/966345790464) * (t0*t2*(1 - t0)*(1 - t2)) + (48445/1277208) * (t0*(1 - t0)*(1 - t1)^2) + (310253265119/966345790464) * (t1^2*t2*(1 - t2)) + (4187545/1277208) * (t1*t2^2*(1 - t1)) + (3501691189919/483172895232) * (t1*t2*(1 - t1)*(1 - t2)) + (2410144/159651) * (t1*(1 - t0)^2*(1 - t1)) + (2117995/638604) * (t1*(1 - t1)*(1 - t2)^2) + (17460693455137/966345790464) * (t2*(1 - t0)^2*(1 - t2)) + (319815145439/966345790464) * (t2*(1 - t1)^2*(1 - t2)) + (48445/9791928) * (t2*(t2 - 1)^2) + (242225/7343946) * ((1 - t2)*(t0 + t1 - 1/8)^2) + (48445/9791928) * ((1 - t2)*(t0 + t1 + t2 - 3)^2) + (8750/2187) * (t1*(t0*t1 - 0)^2) + (1550240/159651) * (t2*(t0*t1 - 0)^2) + (9689021/1277208) * ((1 - t0)*(t0*t1 - 0)^2) + (2966869129/326965248) * (t2*(t0*t2 - 0)^2) + (3443596375/326965248) * ((1 - t0)*(t0*t2 - 0)^2) + (1550240/159651) * ((1 - t2)*(t0*t1 - 1/256)^2) + (22649184832/3487576095) * ((1 - t2)*(t0*t2 - 1/256)^2) + (3443596375/326965248) * (t0*(t0*t2 - 16/25)^2) + (8750/2187) * ((1 - t1)*(t0*t1 - 81/100)^2) + (9689021/1277208) * (t0*(t0*t1 - 1)^2) + (6141908529023/2380851947520) * ((1 - t2)*(t0*t2 - 1)^2)) := by
    rw [hv0, hv1, hv2]
    ring
  rw [hid]
  positivity



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 7
name: C4
reference: A neural network modeled by an adaptive Lotka-Volterra system

-/
theorem box_benchmark_07_c4 :
    ∀ x1 x2 x3 : ℝ,
      (-3 / 2 : ℝ) <= x1 ∧
      x1 <= 2 ∧
      (-3 / 2 : ℝ) <= x2 ∧
      x2 <= 2 ∧
      (-3 / 2 : ℝ) <= x3 ∧
      x3 <= 2 →
        0 <= x1*x2^2 + x1*x3^2 - (11 / 10 : ℝ)*x1 + (207 / 20 : ℝ) := by
  intro x1 x2 x3 ⟨hl0, hu0, hl1, hu1, hl2, hu2⟩
  have htranslated := @result x1 x2 x3 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
