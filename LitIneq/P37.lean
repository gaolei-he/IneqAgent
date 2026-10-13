import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


theorem result (x1 x2 x3 x4 x5 x6 x7 x8 : ℝ) (hl0 : (-1 : ℝ) ≤ x1) (hu0 : x1 ≤ (1 : ℝ)) (hl1 : (-1 : ℝ) ≤ x2) (hu1 : x2 ≤ (1 : ℝ)) (hl2 : (-1 : ℝ) ≤ x3) (hu2 : x3 ≤ (1 : ℝ)) (hl3 : (-1 : ℝ) ≤ x4) (hu3 : x4 ≤ (1 : ℝ)) (hl4 : (-1 : ℝ) ≤ x5) (hu4 : x5 ≤ (1 : ℝ)) (hl5 : (-1 : ℝ) ≤ x6) (hu5 : x6 ≤ (1 : ℝ)) (hl6 : (-1 : ℝ) ≤ x7) (hu6 : x7 ≤ (1 : ℝ)) (hl7 : (-1 : ℝ) ≤ x8) (hu7 : x8 ≤ (1 : ℝ)) : (0 : ℝ) ≤ 29 - 1*x7 + 8*x7^2 - 6*x6*x8 - 2*x1*x4 - 2*x2*x5 - 2*x3*x6 + 2*x1*x7 + 2*x2*x7 + 2*x3*x7 + 2*x4*x7 + 2*x5*x7 + 6*x7*x8 + 8*x6*x7 := by
  let t0 : ℝ := (x1 - (-1)) / (2)
  have ht0 : 0 ≤ t0 := by dsimp [t0]; positivity
  have ht0u : t0 ≤ 1 := by dsimp [t0]; apply (div_le_one (by norm_num)).2; linarith
  have htc0 : 0 ≤ 1 - t0 := sub_nonneg.mpr ht0u
  have hv0 : x1 = (-1) + (2) * t0 := by dsimp [t0]; ring
  let t1 : ℝ := (x2 - (-1)) / (2)
  have ht1 : 0 ≤ t1 := by dsimp [t1]; positivity
  have ht1u : t1 ≤ 1 := by dsimp [t1]; apply (div_le_one (by norm_num)).2; linarith
  have htc1 : 0 ≤ 1 - t1 := sub_nonneg.mpr ht1u
  have hv1 : x2 = (-1) + (2) * t1 := by dsimp [t1]; ring
  let t2 : ℝ := (x3 - (-1)) / (2)
  have ht2 : 0 ≤ t2 := by dsimp [t2]; positivity
  have ht2u : t2 ≤ 1 := by dsimp [t2]; apply (div_le_one (by norm_num)).2; linarith
  have htc2 : 0 ≤ 1 - t2 := sub_nonneg.mpr ht2u
  have hv2 : x3 = (-1) + (2) * t2 := by dsimp [t2]; ring
  let t3 : ℝ := (x4 - (-1)) / (2)
  have ht3 : 0 ≤ t3 := by dsimp [t3]; positivity
  have ht3u : t3 ≤ 1 := by dsimp [t3]; apply (div_le_one (by norm_num)).2; linarith
  have htc3 : 0 ≤ 1 - t3 := sub_nonneg.mpr ht3u
  have hv3 : x4 = (-1) + (2) * t3 := by dsimp [t3]; ring
  let t4 : ℝ := (x5 - (-1)) / (2)
  have ht4 : 0 ≤ t4 := by dsimp [t4]; positivity
  have ht4u : t4 ≤ 1 := by dsimp [t4]; apply (div_le_one (by norm_num)).2; linarith
  have htc4 : 0 ≤ 1 - t4 := sub_nonneg.mpr ht4u
  have hv4 : x5 = (-1) + (2) * t4 := by dsimp [t4]; ring
  let t5 : ℝ := (x6 - (-1)) / (2)
  have ht5 : 0 ≤ t5 := by dsimp [t5]; positivity
  have ht5u : t5 ≤ 1 := by dsimp [t5]; apply (div_le_one (by norm_num)).2; linarith
  have htc5 : 0 ≤ 1 - t5 := sub_nonneg.mpr ht5u
  have hv5 : x6 = (-1) + (2) * t5 := by dsimp [t5]; ring
  let t6 : ℝ := (x7 - (-1)) / (2)
  have ht6 : 0 ≤ t6 := by dsimp [t6]; positivity
  have ht6u : t6 ≤ 1 := by dsimp [t6]; apply (div_le_one (by norm_num)).2; linarith
  have htc6 : 0 ≤ 1 - t6 := sub_nonneg.mpr ht6u
  have hv6 : x7 = (-1) + (2) * t6 := by dsimp [t6]; ring
  let t7 : ℝ := (x8 - (-1)) / (2)
  have ht7 : 0 ≤ t7 := by dsimp [t7]; positivity
  have ht7u : t7 ≤ 1 := by dsimp [t7]; apply (div_le_one (by norm_num)).2; linarith
  have htc7 : 0 ≤ 1 - t7 := sub_nonneg.mpr ht7u
  have hv7 : x8 = (-1) + (2) * t7 := by dsimp [t7]; ring
  have hid : (29 - 1*x7 + 8*x7^2 - 6*x6*x8 - 2*x1*x4 - 2*x2*x5 - 2*x3*x6 + 2*x1*x7 + 2*x2*x7 + 2*x3*x7 + 2*x4*x7 + 2*x5*x7 + 6*x7*x8 + 8*x6*x7) = ((0) + (8) * (t0*(1 - t3)) + (19/3) * (t2*(1 - t2)) + (8) * (t3*t6) + (8) * (t4*t6) + (44904776/18832311) * (t6*t7) + (8) * ((1 - t0)*(1 - t6)) + (8) * ((1 - t1)*(1 - t6)) + (426197536/282484665) * ((1 - t6)^2) + (8) * (t1^2*(1 - t4)) + (8) * (t1*(1 - t1)*(1 - t4)) + (41640392/3323349) * (t5^2*(1 - t5)) + (1144874/1107783) * (t5*(1 - t2)*(1 - t7)) + (41640392/3323349) * (t5*(1 - t5)^2) + (256/135) * ((1 - t2)*(1 - t6)^2) + (256/15) * ((1 - t5)*(1 - t6)^2) + (3256565504/282484665) * ((1 - t6)^2*(1 - t7)) + (5237719/6646698) * (t2*(t2 - t5)^2) + (572437/2215566) * (t7*(t2 - t5)^2) + (200/81) * (t6*(t2 - 0)^2) + (9364562/3323349) * ((1 - t5)*(t2 - 0)^2) + (12720959/1107783) * ((1 - t7)*(t5 - 0)^2) + (256/135) * (t2*(t6 - 1/16)^2) + (256/15) * (t5*(t6 - 1/16)^2) + (3256565504/282484665) * (t7*(t6 - 1/16)^2) + (19840000/3323349) * (t5*(t2 - 607/800)^2) + (200/81) * ((1 - t6)*(t2 - 9/10)^2) + (12720959/1107783) * (t7*(t5 - 1)^2) + (5237719/6646698) * ((1 - t2)*(t2 + t5 - 0)^2) + (572437/2215566) * ((1 - t7)*(t2 + t5 - 0)^2)) := by
    rw [hv0, hv1, hv2, hv3, hv4, hv5, hv6, hv7]
    ring
  rw [hid]
  positivity



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 37
id: A17
name: Viras 8
reference: An efficient algorithm for range computation of polynomials using the Bernstein form
reference_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: -2*x1*x4 + 2*x1*x7 - 2*x2*x5 + 2*x2*x7 - 2*x3*x6 + 2*x3*x7 + 2*x4*x7 + 2*x5*x7 + 8*x6*x7 - 6*x6*x8 + 8*x7^2 + 6*x7*x8 - x7 + 29
source_location: Table 1 Ex 17; Appendix A Problem 17

-/
theorem box_benchmark_37_a17_viras_8 :
    ∀ x1 x2 x3 x4 x5 x6 x7 x8 : ℝ,
      -1 <= x1 ∧
      x1 <= 1 ∧
      -1 <= x2 ∧
      x2 <= 1 ∧
      -1 <= x3 ∧
      x3 <= 1 ∧
      -1 <= x4 ∧
      x4 <= 1 ∧
      -1 <= x5 ∧
      x5 <= 1 ∧
      -1 <= x6 ∧
      x6 <= 1 ∧
      -1 <= x7 ∧
      x7 <= 1 ∧
      -1 <= x8 ∧
      x8 <= 1 →
        0 <= 29 - 1*x7 + 8*x7^2 - 6*x6*x8 - 2*x1*x4 - 2*x2*x5 - 2*x3*x6 + 2*x1*x7 + 2*x2*x7 + 2*x3*x7 + 2*x4*x7 + 2*x5*x7 + 6*x7*x8 + 8*x6*x7 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4, hl5, hu5, hl6, hu6, hl7, hu7⟩
  have htranslated := @result x1 x2 x3 x4 x5 x6 x7 x8 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num) (by convert hl5 using 1 <;> norm_num) (by convert hu5 using 1 <;> norm_num) (by convert hl6 using 1 <;> norm_num) (by convert hu6 using 1 <;> norm_num) (by convert hl7 using 1 <;> norm_num) (by convert hu7 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
