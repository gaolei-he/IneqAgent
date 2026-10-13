import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 : ℝ) (hl0 : (-5 : ℝ) ≤ x1) (hu0 : x1 ≤ (5 : ℝ)) (hl1 : (-5 : ℝ) ≤ x2) (hu1 : x2 ≤ (5 : ℝ)) (hl2 : (-5 : ℝ) ≤ x3) (hu2 : x3 ≤ (5 : ℝ)) : (0 : ℝ) ≤ -x1 - 417817267/500000000*x2^2 + 582182733/500000000*x2 - x3 + 367126907/10000000 := by
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
  have hid : (-x1 - 417817267/500000000*x2^2 + 582182733/500000000*x2 - x3 + 367126907/10000000) = ((1/50000000) + (10) * ((1 - t2)) + (582182733/50000000) * (t0*t1) + (10) * ((1 - t0)*(1 - t1)) + (1082182733/50000000) * (t0*t1*(1 - t0)) + (1082182733/25000000) * (t0*t1*(1 - t1)) + (503451801/12500000) * ((1 - t1)*(t1 - 0)^2) + (931624471/50000000) * (t1*(t1 - 1)^2) + (1082182733/50000000) * (t1*(t0 + t1 - 2)^2)) := by
    rw [hv0, hv1, hv2]
    ring
  rw [hid]
  positivity



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 6
name: 3-Variable Reaction Diffusion
reference: Formalization of Bernstein Polynomials and Applications to Global Optimization / A Tool for Formal Verification of Nonlinear Inequalities
reference_url: https://doi.org/10.1007/s10817-012-9256-3

-/
theorem box_benchmark_06_3_variable_reaction_diffusion :
    ∀ x1 x2 x3 : ℝ,
      -5 <= x1 ∧
      x1 <= 5 ∧
      -5 <= x2 ∧
      x2 <= 5 ∧
      -5 <= x3 ∧
      x3 <= 5 →
        0 <= -x1 - (417817267 / 500000000 : ℝ)*x2^2 + (582182733 / 500000000 : ℝ)*x2 - x3 + (367126907 / 10000000 : ℝ) := by
  intro x1 x2 x3 ⟨hl0, hu0, hl1, hu1, hl2, hu2⟩
  have htranslated := @result x1 x2 x3 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
