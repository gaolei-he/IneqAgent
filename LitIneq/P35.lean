import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


private theorem affine_nonneg (a b t : ℝ) (hl : -1 ≤ t) (hu : t ≤ 1)
    (hm : 0 ≤ a-b) (hp : 0 ≤ a+b) : 0 ≤ a+b*t := by
  have h1 : 0 ≤ 1-t := by linarith
  have h2 : 0 ≤ 1+t := by linarith
  have h3 := mul_nonneg hm h1
  have h4 := mul_nonneg hp h2
  nlinarith only [h3, h4]

private theorem vertex_0  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_1  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_2 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 6*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-6) := by
    convert vertex_0   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-6) := by
    convert vertex_1   using 1 <;> ring
  have hc := affine_nonneg (6) (-6) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_3  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_4  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_5 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4*x7 + 4 := by
  have hm : (0 : ℝ) ≤ (4) - (4) := by
    convert vertex_3   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (4) := by
    convert vertex_4   using 1 <;> ring
  have hc := affine_nonneg (4) (4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_6 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 5*x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (5*x7 - 1) := by
    convert vertex_2 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (5*x7 - 1) := by
    convert vertex_5 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (5*x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_7  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_8  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_9 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4*x7 + 4 := by
  have hm : (0 : ℝ) ≤ (4) - (4) := by
    convert vertex_7   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (4) := by
    convert vertex_8   using 1 <;> ring
  have hc := affine_nonneg (4) (4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_10  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_11  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_12 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_10   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_11   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_13 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (1 - 3*x7) := by
    convert vertex_9 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (1 - 3*x7) := by
    convert vertex_12 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (1 - 3*x7) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_14 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -4*x5*x6*x7 + x5*x6 + x5*x7 + x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x6*x7 + 5) - (-4*x6*x7 + x6 + x7) := by
    convert vertex_6 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7 + 5) + (-4*x6*x7 + x6 + x7) := by
    convert vertex_13 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x6*x7 + 5) (-4*x6*x7 + x6 + x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_15  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_16  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_17 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4*x7 + 4 := by
  have hm : (0 : ℝ) ≤ (4) - (4) := by
    convert vertex_15   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (4) := by
    convert vertex_16   using 1 <;> ring
  have hc := affine_nonneg (4) (4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_18  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_19  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_20 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_18   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_19   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_21 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (1 - 3*x7) := by
    convert vertex_17 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (1 - 3*x7) := by
    convert vertex_20 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (1 - 3*x7) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_22  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_23  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_24 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_22   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_23   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_25  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_26  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_27 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_25   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_26   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_28 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (x7 - 1) := by
    convert vertex_24 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (x7 - 1) := by
    convert vertex_27 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_29 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x5*x6*x7 - x5*x6 - x5*x7 - x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x6*x7 + 5) - (2*x6*x7 - x6 - x7) := by
    convert vertex_21 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7 + 5) + (2*x6*x7 - x6 - x7) := by
    convert vertex_28 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7 + 5) (2*x6*x7 - x6 - x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_30 (x4 x5 x6 x7 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 3*x4*x5*x6*x7 - x4*x5*x6 - x4*x5*x7 - x4*x6*x7 - x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x5*x6*x7 + 5) - (3*x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) := by
    convert vertex_14 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x5*x6*x7 + 5) + (3*x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) := by
    convert vertex_29 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x5*x6*x7 + 5) (3*x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_31  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_32  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_33 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4*x7 + 4 := by
  have hm : (0 : ℝ) ≤ (4) - (4) := by
    convert vertex_31   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (4) := by
    convert vertex_32   using 1 <;> ring
  have hc := affine_nonneg (4) (4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_34  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_35  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_36 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_34   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_35   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_37 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (1 - 3*x7) := by
    convert vertex_33 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (1 - 3*x7) := by
    convert vertex_36 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (1 - 3*x7) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_38  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_39  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_40 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_38   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_39   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_41  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_42  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_43 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_41   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_42   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_44 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (x7 - 1) := by
    convert vertex_40 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (x7 - 1) := by
    convert vertex_43 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_45 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x5*x6*x7 - x5*x6 - x5*x7 - x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x6*x7 + 5) - (2*x6*x7 - x6 - x7) := by
    convert vertex_37 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7 + 5) + (2*x6*x7 - x6 - x7) := by
    convert vertex_44 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7 + 5) (2*x6*x7 - x6 - x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_46  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_47  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_48 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_46   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_47   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_49  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_50  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_51 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_49   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_50   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_52 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (x7 - 1) := by
    convert vertex_48 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (x7 - 1) := by
    convert vertex_51 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_53  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_54  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_55 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_53   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_54   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_56  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_57  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_58 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_56   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_57   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_59 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (x7 + 1) := by
    convert vertex_55 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (x7 + 1) := by
    convert vertex_58 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (x7 + 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_60 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x5*x6 + x5*x7 + x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x6*x7 + 5) - (x6 + x7) := by
    convert vertex_52 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7 + 5) + (x6 + x7) := by
    convert vertex_59 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x6*x7 + 5) (x6 + x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_61 (x4 x5 x6 x7 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7 + x4*x5*x6 + x4*x5*x7 + x4*x6*x7 + x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x5*x6*x7 + 5) - (-x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) := by
    convert vertex_45 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x5*x6*x7 + 5) + (-x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) := by
    convert vertex_60 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x5*x6*x7 + 5) (-x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_62 (x3 x4 x5 x6 x7 : ℝ) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -2*x3*x4*x5*x6*x7 + x3*x4*x5*x6 + x3*x4*x5*x7 + x3*x4*x6*x7 + x3*x5*x6*x7 + x4*x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x4*x5*x6*x7 + 5) - (-2*x4*x5*x6*x7 + x4*x5*x6 + x4*x5*x7 + x4*x6*x7 + x5*x6*x7) := by
    convert vertex_30 x4 x5 x6 x7 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x4*x5*x6*x7 + 5) + (-2*x4*x5*x6*x7 + x4*x5*x6 + x4*x5*x7 + x4*x6*x7 + x5*x6*x7) := by
    convert vertex_61 x4 x5 x6 x7 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x4*x5*x6*x7 + 5) (-2*x4*x5*x6*x7 + x4*x5*x6 + x4*x5*x7 + x4*x6*x7 + x5*x6*x7) x3 hl_x3 hu_x3 hm hp
  convert hc using 1 <;> ring

private theorem vertex_63  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_64  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_65 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4*x7 + 4 := by
  have hm : (0 : ℝ) ≤ (4) - (4) := by
    convert vertex_63   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (4) := by
    convert vertex_64   using 1 <;> ring
  have hc := affine_nonneg (4) (4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_66  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_67  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_68 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_66   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_67   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_69 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (1 - 3*x7) := by
    convert vertex_65 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (1 - 3*x7) := by
    convert vertex_68 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (1 - 3*x7) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_70  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_71  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_72 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_70   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_71   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_73  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_74  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_75 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_73   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_74   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_76 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (x7 - 1) := by
    convert vertex_72 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (x7 - 1) := by
    convert vertex_75 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_77 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x5*x6*x7 - x5*x6 - x5*x7 - x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x6*x7 + 5) - (2*x6*x7 - x6 - x7) := by
    convert vertex_69 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7 + 5) + (2*x6*x7 - x6 - x7) := by
    convert vertex_76 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7 + 5) (2*x6*x7 - x6 - x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_78  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_79  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_80 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_78   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_79   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_81  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_82  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_83 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_81   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_82   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_84 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (x7 - 1) := by
    convert vertex_80 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (x7 - 1) := by
    convert vertex_83 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_85  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_86  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_87 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_85   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_86   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_88  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_89  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_90 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_88   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_89   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_91 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (x7 + 1) := by
    convert vertex_87 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (x7 + 1) := by
    convert vertex_90 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (x7 + 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_92 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x5*x6 + x5*x7 + x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x6*x7 + 5) - (x6 + x7) := by
    convert vertex_84 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7 + 5) + (x6 + x7) := by
    convert vertex_91 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x6*x7 + 5) (x6 + x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_93 (x4 x5 x6 x7 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7 + x4*x5*x6 + x4*x5*x7 + x4*x6*x7 + x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x5*x6*x7 + 5) - (-x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) := by
    convert vertex_77 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x5*x6*x7 + 5) + (-x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) := by
    convert vertex_92 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x5*x6*x7 + 5) (-x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_94  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_95  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_96 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_94   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_95   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_97  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_98  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_99 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_97   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_98   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_100 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (x7 - 1) := by
    convert vertex_96 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (x7 - 1) := by
    convert vertex_99 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_101  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_102  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_103 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_101   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_102   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_104  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_105  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_106 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_104   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_105   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_107 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (x7 + 1) := by
    convert vertex_103 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (x7 + 1) := by
    convert vertex_106 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (x7 + 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_108 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x5*x6 + x5*x7 + x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x6*x7 + 5) - (x6 + x7) := by
    convert vertex_100 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7 + 5) + (x6 + x7) := by
    convert vertex_107 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x6*x7 + 5) (x6 + x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_109  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_110  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_111 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_109   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_110   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_112  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_113  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_114 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_112   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_113   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_115 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (x7 + 1) := by
    convert vertex_111 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (x7 + 1) := by
    convert vertex_114 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (x7 + 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_116  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_117  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_118 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_116   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_117   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_119  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_120  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_121 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 - 4*x7 := by
  have hm : (0 : ℝ) ≤ (4) - (-4) := by
    convert vertex_119   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (-4) := by
    convert vertex_120   using 1 <;> ring
  have hc := affine_nonneg (4) (-4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_122 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (-3*x7 - 1) := by
    convert vertex_118 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (-3*x7 - 1) := by
    convert vertex_121 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (-3*x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_123 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -2*x5*x6*x7 - x5*x6 - x5*x7 - x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x6*x7 + 5) - (-2*x6*x7 - x6 - x7) := by
    convert vertex_115 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7 + 5) + (-2*x6*x7 - x6 - x7) := by
    convert vertex_122 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7 + 5) (-2*x6*x7 - x6 - x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_124 (x4 x5 x6 x7 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7 - x4*x5*x6 - x4*x5*x7 - x4*x6*x7 - x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x5*x6*x7 + 5) - (-x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) := by
    convert vertex_108 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x5*x6*x7 + 5) + (-x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) := by
    convert vertex_123 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x5*x6*x7 + 5) (-x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_125 (x3 x4 x5 x6 x7 : ℝ) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -x3*x4*x5*x6 - x3*x4*x5*x7 - x3*x4*x6*x7 - x3*x5*x6*x7 - x4*x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x4*x5*x6*x7 + 5) - (-x4*x5*x6 - x4*x5*x7 - x4*x6*x7 - x5*x6*x7) := by
    convert vertex_93 x4 x5 x6 x7 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x4*x5*x6*x7 + 5) + (-x4*x5*x6 - x4*x5*x7 - x4*x6*x7 - x5*x6*x7) := by
    convert vertex_124 x4 x5 x6 x7 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x4*x5*x6*x7 + 5) (-x4*x5*x6 - x4*x5*x7 - x4*x6*x7 - x5*x6*x7) x3 hl_x3 hu_x3 hm hp
  convert hc using 1 <;> ring

private theorem vertex_126 (x2 x3 x4 x5 x6 x7 : ℝ) (hl_x2 : -1 ≤ x2) (hu_x2 : x2 ≤ 1) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x2*x3*x4*x5*x6*x7 - x2*x3*x4*x5*x6 - x2*x3*x4*x5*x7 - x2*x3*x4*x6*x7 - x2*x3*x5*x6*x7 - x2*x4*x5*x6*x7 - x3*x4*x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x3*x4*x5*x6*x7 + 5) - (x3*x4*x5*x6*x7 - x3*x4*x5*x6 - x3*x4*x5*x7 - x3*x4*x6*x7 - x3*x5*x6*x7 - x4*x5*x6*x7) := by
    convert vertex_62 x3 x4 x5 x6 x7 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x3*x4*x5*x6*x7 + 5) + (x3*x4*x5*x6*x7 - x3*x4*x5*x6 - x3*x4*x5*x7 - x3*x4*x6*x7 - x3*x5*x6*x7 - x4*x5*x6*x7) := by
    convert vertex_125 x3 x4 x5 x6 x7 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x3*x4*x5*x6*x7 + 5) (x3*x4*x5*x6*x7 - x3*x4*x5*x6 - x3*x4*x5*x7 - x3*x4*x6*x7 - x3*x5*x6*x7 - x4*x5*x6*x7) x2 hl_x2 hu_x2 hm hp
  convert hc using 1 <;> ring

private theorem vertex_127  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_128  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_129 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4*x7 + 4 := by
  have hm : (0 : ℝ) ≤ (4) - (4) := by
    convert vertex_127   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (4) := by
    convert vertex_128   using 1 <;> ring
  have hc := affine_nonneg (4) (4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_130  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_131  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_132 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_130   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_131   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_133 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (1 - 3*x7) := by
    convert vertex_129 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (1 - 3*x7) := by
    convert vertex_132 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (1 - 3*x7) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_134  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_135  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_136 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_134   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_135   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_137  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_138  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_139 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_137   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_138   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_140 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (x7 - 1) := by
    convert vertex_136 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (x7 - 1) := by
    convert vertex_139 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_141 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x5*x6*x7 - x5*x6 - x5*x7 - x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x6*x7 + 5) - (2*x6*x7 - x6 - x7) := by
    convert vertex_133 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7 + 5) + (2*x6*x7 - x6 - x7) := by
    convert vertex_140 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7 + 5) (2*x6*x7 - x6 - x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_142  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_143  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_144 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_142   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_143   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_145  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_146  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_147 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_145   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_146   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_148 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (x7 - 1) := by
    convert vertex_144 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (x7 - 1) := by
    convert vertex_147 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_149  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_150  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_151 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_149   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_150   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_152  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_153  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_154 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_152   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_153   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_155 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (x7 + 1) := by
    convert vertex_151 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (x7 + 1) := by
    convert vertex_154 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (x7 + 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_156 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x5*x6 + x5*x7 + x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x6*x7 + 5) - (x6 + x7) := by
    convert vertex_148 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7 + 5) + (x6 + x7) := by
    convert vertex_155 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x6*x7 + 5) (x6 + x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_157 (x4 x5 x6 x7 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7 + x4*x5*x6 + x4*x5*x7 + x4*x6*x7 + x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x5*x6*x7 + 5) - (-x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) := by
    convert vertex_141 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x5*x6*x7 + 5) + (-x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) := by
    convert vertex_156 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x5*x6*x7 + 5) (-x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_158  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_159  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_160 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_158   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_159   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_161  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_162  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_163 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_161   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_162   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_164 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (x7 - 1) := by
    convert vertex_160 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (x7 - 1) := by
    convert vertex_163 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_165  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_166  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_167 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_165   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_166   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_168  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_169  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_170 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_168   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_169   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_171 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (x7 + 1) := by
    convert vertex_167 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (x7 + 1) := by
    convert vertex_170 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (x7 + 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_172 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x5*x6 + x5*x7 + x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x6*x7 + 5) - (x6 + x7) := by
    convert vertex_164 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7 + 5) + (x6 + x7) := by
    convert vertex_171 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x6*x7 + 5) (x6 + x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_173  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_174  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_175 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_173   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_174   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_176  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_177  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_178 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_176   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_177   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_179 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (x7 + 1) := by
    convert vertex_175 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (x7 + 1) := by
    convert vertex_178 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (x7 + 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_180  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_181  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_182 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_180   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_181   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_183  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_184  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_185 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 - 4*x7 := by
  have hm : (0 : ℝ) ≤ (4) - (-4) := by
    convert vertex_183   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (-4) := by
    convert vertex_184   using 1 <;> ring
  have hc := affine_nonneg (4) (-4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_186 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (-3*x7 - 1) := by
    convert vertex_182 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (-3*x7 - 1) := by
    convert vertex_185 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (-3*x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_187 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -2*x5*x6*x7 - x5*x6 - x5*x7 - x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x6*x7 + 5) - (-2*x6*x7 - x6 - x7) := by
    convert vertex_179 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7 + 5) + (-2*x6*x7 - x6 - x7) := by
    convert vertex_186 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7 + 5) (-2*x6*x7 - x6 - x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_188 (x4 x5 x6 x7 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7 - x4*x5*x6 - x4*x5*x7 - x4*x6*x7 - x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x5*x6*x7 + 5) - (-x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) := by
    convert vertex_172 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x5*x6*x7 + 5) + (-x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) := by
    convert vertex_187 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x5*x6*x7 + 5) (-x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_189 (x3 x4 x5 x6 x7 : ℝ) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -x3*x4*x5*x6 - x3*x4*x5*x7 - x3*x4*x6*x7 - x3*x5*x6*x7 - x4*x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x4*x5*x6*x7 + 5) - (-x4*x5*x6 - x4*x5*x7 - x4*x6*x7 - x5*x6*x7) := by
    convert vertex_157 x4 x5 x6 x7 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x4*x5*x6*x7 + 5) + (-x4*x5*x6 - x4*x5*x7 - x4*x6*x7 - x5*x6*x7) := by
    convert vertex_188 x4 x5 x6 x7 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x4*x5*x6*x7 + 5) (-x4*x5*x6 - x4*x5*x7 - x4*x6*x7 - x5*x6*x7) x3 hl_x3 hu_x3 hm hp
  convert hc using 1 <;> ring

private theorem vertex_190  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_191  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_192 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6 - 2*x7 := by
  have hm : (0 : ℝ) ≤ (6) - (-2) := by
    convert vertex_190   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (-2) := by
    convert vertex_191   using 1 <;> ring
  have hc := affine_nonneg (6) (-2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_193  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_194  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_195 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_193   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_194   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_196 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (x7 - 1) := by
    convert vertex_192 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (x7 - 1) := by
    convert vertex_195 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_197  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_198  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_199 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_197   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_198   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_200  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_201  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_202 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_200   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_201   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_203 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (x7 + 1) := by
    convert vertex_199 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (x7 + 1) := by
    convert vertex_202 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (x7 + 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_204 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x5*x6 + x5*x7 + x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x6*x7 + 5) - (x6 + x7) := by
    convert vertex_196 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7 + 5) + (x6 + x7) := by
    convert vertex_203 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x6*x7 + 5) (x6 + x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_205  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_206  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_207 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_205   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_206   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_208  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_209  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_210 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_208   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_209   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_211 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (x7 + 1) := by
    convert vertex_207 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (x7 + 1) := by
    convert vertex_210 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (x7 + 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_212  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_213  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_214 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_212   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_213   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_215  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_216  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_217 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 - 4*x7 := by
  have hm : (0 : ℝ) ≤ (4) - (-4) := by
    convert vertex_215   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (-4) := by
    convert vertex_216   using 1 <;> ring
  have hc := affine_nonneg (4) (-4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_218 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (-3*x7 - 1) := by
    convert vertex_214 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (-3*x7 - 1) := by
    convert vertex_217 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (-3*x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_219 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -2*x5*x6*x7 - x5*x6 - x5*x7 - x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x6*x7 + 5) - (-2*x6*x7 - x6 - x7) := by
    convert vertex_211 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7 + 5) + (-2*x6*x7 - x6 - x7) := by
    convert vertex_218 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7 + 5) (-2*x6*x7 - x6 - x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_220 (x4 x5 x6 x7 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7 - x4*x5*x6 - x4*x5*x7 - x4*x6*x7 - x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x5*x6*x7 + 5) - (-x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) := by
    convert vertex_204 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x5*x6*x7 + 5) + (-x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) := by
    convert vertex_219 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x5*x6*x7 + 5) (-x5*x6*x7 - x5*x6 - x5*x7 - x6*x7) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_221  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_222  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_223 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 := by
  have hm : (0 : ℝ) ≤ (4) - (0) := by
    convert vertex_221   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (0) := by
    convert vertex_222   using 1 <;> ring
  have hc := affine_nonneg (4) (0) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_224  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_225  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_226 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_224   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_225   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_227 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (x7 + 1) := by
    convert vertex_223 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (x7 + 1) := by
    convert vertex_226 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (x7 + 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_228  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_229  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_230 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_228   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_229   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_231  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_232  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_233 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 - 4*x7 := by
  have hm : (0 : ℝ) ≤ (4) - (-4) := by
    convert vertex_231   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (-4) := by
    convert vertex_232   using 1 <;> ring
  have hc := affine_nonneg (4) (-4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_234 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (-3*x7 - 1) := by
    convert vertex_230 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (-3*x7 - 1) := by
    convert vertex_233 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (-3*x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_235 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -2*x5*x6*x7 - x5*x6 - x5*x7 - x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (-x6*x7 + 5) - (-2*x6*x7 - x6 - x7) := by
    convert vertex_227 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7 + 5) + (-2*x6*x7 - x6 - x7) := by
    convert vertex_234 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7 + 5) (-2*x6*x7 - x6 - x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_236  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_237  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_238 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (2) := by
    convert vertex_236   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (2) := by
    convert vertex_237   using 1 <;> ring
  have hc := affine_nonneg (6) (2) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_239  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_240  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_241 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 - 4*x7 := by
  have hm : (0 : ℝ) ≤ (4) - (-4) := by
    convert vertex_239   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (-4) := by
    convert vertex_240   using 1 <;> ring
  have hc := affine_nonneg (4) (-4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_242 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7 - x6 - x7 + 5 := by
  have hm : (0 : ℝ) ≤ (5 - x7) - (-3*x7 - 1) := by
    convert vertex_238 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (5 - x7) + (-3*x7 - 1) := by
    convert vertex_241 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (5 - x7) (-3*x7 - 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_243  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_244  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_245 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4 - 4*x7 := by
  have hm : (0 : ℝ) ≤ (4) - (-4) := by
    convert vertex_243   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (4) + (-4) := by
    convert vertex_244   using 1 <;> ring
  have hc := affine_nonneg (4) (-4) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_246  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_247  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_248 (x7 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 6*x7 + 6 := by
  have hm : (0 : ℝ) ≤ (6) - (6) := by
    convert vertex_246   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (6) + (6) := by
    convert vertex_247   using 1 <;> ring
  have hc := affine_nonneg (6) (6) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_249 (x6 x7 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 5*x6*x7 + x6 + x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x7 + 5) - (5*x7 + 1) := by
    convert vertex_245 x7 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7 + 5) + (5*x7 + 1) := by
    convert vertex_248 x7 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x7 + 5) (5*x7 + 1) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_250 (x5 x6 x7 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 4*x5*x6*x7 + x5*x6 + x5*x7 + x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x6*x7 + 5) - (4*x6*x7 + x6 + x7) := by
    convert vertex_242 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7 + 5) + (4*x6*x7 + x6 + x7) := by
    convert vertex_249 x6 x7 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x6*x7 + 5) (4*x6*x7 + x6 + x7) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_251 (x4 x5 x6 x7 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 3*x4*x5*x6*x7 + x4*x5*x6 + x4*x5*x7 + x4*x6*x7 + x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x5*x6*x7 + 5) - (3*x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) := by
    convert vertex_235 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x5*x6*x7 + 5) + (3*x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) := by
    convert vertex_250 x5 x6 x7 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x5*x6*x7 + 5) (3*x5*x6*x7 + x5*x6 + x5*x7 + x6*x7) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_252 (x3 x4 x5 x6 x7 : ℝ) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ 2*x3*x4*x5*x6*x7 + x3*x4*x5*x6 + x3*x4*x5*x7 + x3*x4*x6*x7 + x3*x5*x6*x7 + x4*x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x4*x5*x6*x7 + 5) - (2*x4*x5*x6*x7 + x4*x5*x6 + x4*x5*x7 + x4*x6*x7 + x5*x6*x7) := by
    convert vertex_220 x4 x5 x6 x7 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x4*x5*x6*x7 + 5) + (2*x4*x5*x6*x7 + x4*x5*x6 + x4*x5*x7 + x4*x6*x7 + x5*x6*x7) := by
    convert vertex_251 x4 x5 x6 x7 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x4*x5*x6*x7 + 5) (2*x4*x5*x6*x7 + x4*x5*x6 + x4*x5*x7 + x4*x6*x7 + x5*x6*x7) x3 hl_x3 hu_x3 hm hp
  convert hc using 1 <;> ring

private theorem vertex_253 (x2 x3 x4 x5 x6 x7 : ℝ) (hl_x2 : -1 ≤ x2) (hu_x2 : x2 ≤ 1) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x2*x3*x4*x5*x6*x7 + x2*x3*x4*x5*x6 + x2*x3*x4*x5*x7 + x2*x3*x4*x6*x7 + x2*x3*x5*x6*x7 + x2*x4*x5*x6*x7 + x3*x4*x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x3*x4*x5*x6*x7 + 5) - (x3*x4*x5*x6*x7 + x3*x4*x5*x6 + x3*x4*x5*x7 + x3*x4*x6*x7 + x3*x5*x6*x7 + x4*x5*x6*x7) := by
    convert vertex_189 x3 x4 x5 x6 x7 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x3*x4*x5*x6*x7 + 5) + (x3*x4*x5*x6*x7 + x3*x4*x5*x6 + x3*x4*x5*x7 + x3*x4*x6*x7 + x3*x5*x6*x7 + x4*x5*x6*x7) := by
    convert vertex_252 x3 x4 x5 x6 x7 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x3*x4*x5*x6*x7 + 5) (x3*x4*x5*x6*x7 + x3*x4*x5*x6 + x3*x4*x5*x7 + x3*x4*x6*x7 + x3*x5*x6*x7 + x4*x5*x6*x7) x2 hl_x2 hu_x2 hm hp
  convert hc using 1 <;> ring

private theorem vertex_254 (x1 x2 x3 x4 x5 x6 x7 : ℝ) (hl_x1 : -1 ≤ x1) (hu_x1 : x1 ≤ 1) (hl_x2 : -1 ≤ x2) (hu_x2 : x2 ≤ 1) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) : (0 : ℝ) ≤ x1*x2*x3*x4*x5*x6 + x1*x2*x3*x4*x5*x7 + x1*x2*x3*x4*x6*x7 + x1*x2*x3*x5*x6*x7 + x1*x2*x4*x5*x6*x7 + x1*x3*x4*x5*x6*x7 + x2*x3*x4*x5*x6*x7 + 5 := by
  have hm : (0 : ℝ) ≤ (x2*x3*x4*x5*x6*x7 + 5) - (x2*x3*x4*x5*x6 + x2*x3*x4*x5*x7 + x2*x3*x4*x6*x7 + x2*x3*x5*x6*x7 + x2*x4*x5*x6*x7 + x3*x4*x5*x6*x7) := by
    convert vertex_126 x2 x3 x4 x5 x6 x7 hl_x2 hu_x2 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x2*x3*x4*x5*x6*x7 + 5) + (x2*x3*x4*x5*x6 + x2*x3*x4*x5*x7 + x2*x3*x4*x6*x7 + x2*x3*x5*x6*x7 + x2*x4*x5*x6*x7 + x3*x4*x5*x6*x7) := by
    convert vertex_253 x2 x3 x4 x5 x6 x7 hl_x2 hu_x2 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 using 1 <;> ring
  have hc := affine_nonneg (x2*x3*x4*x5*x6*x7 + 5) (x2*x3*x4*x5*x6 + x2*x3*x4*x5*x7 + x2*x3*x4*x6*x7 + x2*x3*x5*x6*x7 + x2*x4*x5*x6*x7 + x3*x4*x5*x6*x7) x1 hl_x1 hu_x1 hm hp
  convert hc using 1 <;> ring
theorem result (x1 x2 x3 x4 x5 x6 x7 : ℝ) (hl0 : (-1 : ℝ) ≤ x1) (hu0 : x1 ≤ (1 : ℝ)) (hl1 : (-1 : ℝ) ≤ x2) (hu1 : x2 ≤ (1 : ℝ)) (hl2 : (-1 : ℝ) ≤ x3) (hu2 : x3 ≤ (1 : ℝ)) (hl3 : (-1 : ℝ) ≤ x4) (hu3 : x4 ≤ (1 : ℝ)) (hl4 : (-1 : ℝ) ≤ x5) (hu4 : x5 ≤ (1 : ℝ)) (hl5 : (-1 : ℝ) ≤ x6) (hu5 : x6 ≤ (1 : ℝ)) (hl6 : (-1 : ℝ) ≤ x7) (hu6 : x7 ≤ (1 : ℝ)) : (0 : ℝ) ≤ 5 + x1*x2*x3*x4*x5*x6 + x1*x2*x3*x4*x5*x7 + x1*x2*x3*x4*x6*x7 + x1*x2*x3*x5*x6*x7 + x1*x2*x4*x5*x6*x7 + x1*x3*x4*x5*x6*x7 + x2*x3*x4*x5*x6*x7 := by
  convert vertex_254 x1 x2 x3 x4 x5 x6 x7 hl0 hu0 hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4 hl5 hu5 hl6 hu6 using 1 <;> ring



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 35
id: A15
name: Cyc 7
reference: An efficient algorithm for range computation of polynomials using the Bernstein form
reference_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: x1*x2*x3*x4*x5*x6 + x2*x3*x4*x5*x6*x7 + x1*x3*x4*x5*x6*x7 + x1*x2*x4*x5*x6*x7 + x1*x2*x3*x5*x6*x7 + x1*x2*x3*x4*x6*x7 + x1*x2*x3*x4*x5*x7 + 5
source_location: Table 1 Ex 15; Appendix A Problem 15

-/
theorem box_benchmark_35_a15_cyc_7 :
    ∀ x1 x2 x3 x4 x5 x6 x7 : ℝ,
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
      x7 <= 1 →
        0 <= 5 + x1*x2*x3*x4*x5*x6 + x1*x2*x3*x4*x5*x7 + x1*x2*x3*x4*x6*x7 + x1*x2*x3*x5*x6*x7 + x1*x2*x4*x5*x6*x7 + x1*x3*x4*x5*x6*x7 + x2*x3*x4*x5*x6*x7 := by
  intro x1 x2 x3 x4 x5 x6 x7 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4, hl5, hu5, hl6, hu6⟩
  have htranslated := @result x1 x2 x3 x4 x5 x6 x7 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num) (by convert hl5 using 1 <;> norm_num) (by convert hu5 using 1 <;> norm_num) (by convert hl6 using 1 <;> norm_num) (by convert hu6 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
