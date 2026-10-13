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

private theorem vertex_0  : (0 : ℝ) ≤ 0 := by
  norm_num

private theorem vertex_1  : (0 : ℝ) ≤ 14 := by
  norm_num

private theorem vertex_2 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (7) := by
    convert vertex_0   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (7) := by
    convert vertex_1   using 1 <;> ring
  have hc := affine_nonneg (7) (7) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_3  : (0 : ℝ) ≤ 14 := by
  norm_num

private theorem vertex_4  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_5 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-5) := by
    convert vertex_3   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-5) := by
    convert vertex_4   using 1 <;> ring
  have hc := affine_nonneg (9) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_6 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -6*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 6*x8) := by
    convert vertex_2 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 6*x8) := by
    convert vertex_5 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 6*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_7  : (0 : ℝ) ≤ 14 := by
  norm_num

private theorem vertex_8  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_9 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-5) := by
    convert vertex_7   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-5) := by
    convert vertex_8   using 1 <;> ring
  have hc := affine_nonneg (9) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_10  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_11  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_12 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_10   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_11   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_13 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (4*x8 - 1) := by
    convert vertex_9 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (4*x8 - 1) := by
    convert vertex_12 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_14 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 5*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (5*x7*x8 - x7 - x8) := by
    convert vertex_6 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (5*x7*x8 - x7 - x8) := by
    convert vertex_13 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (5*x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_15  : (0 : ℝ) ≤ 14 := by
  norm_num

private theorem vertex_16  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_17 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-5) := by
    convert vertex_15   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-5) := by
    convert vertex_16   using 1 <;> ring
  have hc := affine_nonneg (9) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_18  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_19  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_20 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_18   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_19   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_21 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (4*x8 - 1) := by
    convert vertex_17 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (4*x8 - 1) := by
    convert vertex_20 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_22  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_23  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_24 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_22   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_23   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_25  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_26  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_27 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_25   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_26   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_28 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_24 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_27 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_29 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (-3*x7*x8 + x7 + x8) := by
    convert vertex_21 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (-3*x7*x8 + x7 + x8) := by
    convert vertex_28 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (-3*x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_30 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -4*x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x6*x7*x8 + 8) - (-4*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_14 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7*x8 + 8) + (-4*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_29 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x6*x7*x8 + 8) (-4*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_31  : (0 : ℝ) ≤ 14 := by
  norm_num

private theorem vertex_32  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_33 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-5) := by
    convert vertex_31   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-5) := by
    convert vertex_32   using 1 <;> ring
  have hc := affine_nonneg (9) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_34  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_35  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_36 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_34   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_35   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_37 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (4*x8 - 1) := by
    convert vertex_33 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (4*x8 - 1) := by
    convert vertex_36 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_38  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_39  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_40 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_38   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_39   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_41  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_42  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_43 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_41   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_42   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_44 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_40 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_43 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_45 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (-3*x7*x8 + x7 + x8) := by
    convert vertex_37 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (-3*x7*x8 + x7 + x8) := by
    convert vertex_44 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (-3*x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_46  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_47  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_48 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_46   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_47   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_49  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_50  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_51 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_49   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_50   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_52 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_48 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_51 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_53  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_54  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_55 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_53   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_54   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_56  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_57  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_58 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_56   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_57   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_59 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_55 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_58 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_60 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (x7*x8 - x7 - x8) := by
    convert vertex_52 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (x7*x8 - x7 - x8) := by
    convert vertex_59 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_61 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x6*x7*x8 + 8) - (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_45 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7*x8 + 8) + (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_60 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7*x8 + 8) (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_62 (x4 x5 x6 x7 x8 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x4*x5*x6*x7*x8 - x4*x5*x6*x7 - x4*x5*x6*x8 - x4*x5*x7*x8 - x4*x6*x7*x8 - x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x5*x6*x7*x8 + 8) - (3*x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) := by
    convert vertex_30 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x5*x6*x7*x8 + 8) + (3*x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) := by
    convert vertex_61 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x5*x6*x7*x8 + 8) (3*x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_63  : (0 : ℝ) ≤ 14 := by
  norm_num

private theorem vertex_64  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_65 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-5) := by
    convert vertex_63   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-5) := by
    convert vertex_64   using 1 <;> ring
  have hc := affine_nonneg (9) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_66  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_67  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_68 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_66   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_67   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_69 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (4*x8 - 1) := by
    convert vertex_65 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (4*x8 - 1) := by
    convert vertex_68 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_70  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_71  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_72 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_70   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_71   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_73  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_74  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_75 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_73   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_74   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_76 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_72 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_75 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_77 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (-3*x7*x8 + x7 + x8) := by
    convert vertex_69 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (-3*x7*x8 + x7 + x8) := by
    convert vertex_76 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (-3*x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_78  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_79  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_80 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_78   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_79   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_81  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_82  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_83 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_81   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_82   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_84 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_80 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_83 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_85  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_86  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_87 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_85   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_86   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_88  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_89  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_90 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_88   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_89   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_91 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_87 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_90 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_92 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (x7*x8 - x7 - x8) := by
    convert vertex_84 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (x7*x8 - x7 - x8) := by
    convert vertex_91 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_93 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x6*x7*x8 + 8) - (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_77 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7*x8 + 8) + (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_92 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7*x8 + 8) (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_94  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_95  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_96 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_94   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_95   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_97  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_98  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_99 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_97   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_98   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_100 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_96 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_99 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_101  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_102  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_103 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_101   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_102   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_104  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_105  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_106 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_104   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_105   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_107 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_103 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_106 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_108 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (x7*x8 - x7 - x8) := by
    convert vertex_100 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (x7*x8 - x7 - x8) := by
    convert vertex_107 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_109  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_110  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_111 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_109   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_110   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_112  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_113  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_114 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_112   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_113   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_115 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_111 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_114 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_116  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_117  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_118 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_116   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_117   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_119  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_120  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_121 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_119   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_120   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_122 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_118 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_121 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_123 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (x7*x8 + x7 + x8) := by
    convert vertex_115 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (x7*x8 + x7 + x8) := by
    convert vertex_122 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_124 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x6*x7*x8 + 8) - (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_108 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7*x8 + 8) + (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_123 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x6*x7*x8 + 8) (x6*x7 + x6*x8 + x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_125 (x4 x5 x6 x7 x8 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7*x8 + x4*x5*x6*x7 + x4*x5*x6*x8 + x4*x5*x7*x8 + x4*x6*x7*x8 + x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x5*x6*x7*x8 + 8) - (-x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) := by
    convert vertex_93 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x5*x6*x7*x8 + 8) + (-x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) := by
    convert vertex_124 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x5*x6*x7*x8 + 8) (-x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_126 (x3 x4 x5 x6 x7 x8 : ℝ) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x3*x4*x5*x6*x7*x8 + x3*x4*x5*x6*x7 + x3*x4*x5*x6*x8 + x3*x4*x5*x7*x8 + x3*x4*x6*x7*x8 + x3*x5*x6*x7*x8 + x4*x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x4*x5*x6*x7*x8 + 8) - (-2*x4*x5*x6*x7*x8 + x4*x5*x6*x7 + x4*x5*x6*x8 + x4*x5*x7*x8 + x4*x6*x7*x8 + x5*x6*x7*x8) := by
    convert vertex_62 x4 x5 x6 x7 x8 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x4*x5*x6*x7*x8 + 8) + (-2*x4*x5*x6*x7*x8 + x4*x5*x6*x7 + x4*x5*x6*x8 + x4*x5*x7*x8 + x4*x6*x7*x8 + x5*x6*x7*x8) := by
    convert vertex_125 x4 x5 x6 x7 x8 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x4*x5*x6*x7*x8 + 8) (-2*x4*x5*x6*x7*x8 + x4*x5*x6*x7 + x4*x5*x6*x8 + x4*x5*x7*x8 + x4*x6*x7*x8 + x5*x6*x7*x8) x3 hl_x3 hu_x3 hm hp
  convert hc using 1 <;> ring

private theorem vertex_127  : (0 : ℝ) ≤ 14 := by
  norm_num

private theorem vertex_128  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_129 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-5) := by
    convert vertex_127   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-5) := by
    convert vertex_128   using 1 <;> ring
  have hc := affine_nonneg (9) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_130  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_131  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_132 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_130   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_131   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_133 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (4*x8 - 1) := by
    convert vertex_129 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (4*x8 - 1) := by
    convert vertex_132 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_134  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_135  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_136 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_134   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_135   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_137  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_138  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_139 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_137   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_138   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_140 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_136 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_139 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_141 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (-3*x7*x8 + x7 + x8) := by
    convert vertex_133 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (-3*x7*x8 + x7 + x8) := by
    convert vertex_140 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (-3*x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_142  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_143  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_144 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_142   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_143   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_145  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_146  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_147 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_145   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_146   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_148 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_144 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_147 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_149  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_150  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_151 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_149   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_150   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_152  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_153  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_154 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_152   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_153   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_155 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_151 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_154 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_156 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (x7*x8 - x7 - x8) := by
    convert vertex_148 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (x7*x8 - x7 - x8) := by
    convert vertex_155 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_157 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x6*x7*x8 + 8) - (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_141 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7*x8 + 8) + (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_156 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7*x8 + 8) (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_158  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_159  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_160 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_158   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_159   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_161  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_162  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_163 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_161   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_162   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_164 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_160 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_163 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_165  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_166  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_167 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_165   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_166   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_168  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_169  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_170 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_168   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_169   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_171 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_167 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_170 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_172 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (x7*x8 - x7 - x8) := by
    convert vertex_164 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (x7*x8 - x7 - x8) := by
    convert vertex_171 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_173  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_174  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_175 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_173   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_174   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_176  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_177  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_178 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_176   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_177   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_179 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_175 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_178 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_180  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_181  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_182 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_180   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_181   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_183  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_184  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_185 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_183   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_184   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_186 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_182 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_185 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_187 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (x7*x8 + x7 + x8) := by
    convert vertex_179 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (x7*x8 + x7 + x8) := by
    convert vertex_186 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_188 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x6*x7*x8 + 8) - (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_172 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7*x8 + 8) + (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_187 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x6*x7*x8 + 8) (x6*x7 + x6*x8 + x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_189 (x4 x5 x6 x7 x8 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7*x8 + x4*x5*x6*x7 + x4*x5*x6*x8 + x4*x5*x7*x8 + x4*x6*x7*x8 + x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x5*x6*x7*x8 + 8) - (-x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) := by
    convert vertex_157 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x5*x6*x7*x8 + 8) + (-x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) := by
    convert vertex_188 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x5*x6*x7*x8 + 8) (-x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_190  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_191  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_192 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_190   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_191   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_193  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_194  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_195 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_193   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_194   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_196 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_192 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_195 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_197  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_198  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_199 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_197   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_198   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_200  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_201  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_202 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_200   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_201   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_203 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_199 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_202 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_204 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (x7*x8 - x7 - x8) := by
    convert vertex_196 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (x7*x8 - x7 - x8) := by
    convert vertex_203 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_205  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_206  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_207 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_205   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_206   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_208  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_209  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_210 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_208   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_209   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_211 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_207 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_210 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_212  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_213  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_214 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_212   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_213   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_215  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_216  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_217 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_215   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_216   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_218 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_214 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_217 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_219 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (x7*x8 + x7 + x8) := by
    convert vertex_211 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (x7*x8 + x7 + x8) := by
    convert vertex_218 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_220 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x6*x7*x8 + 8) - (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_204 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7*x8 + 8) + (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_219 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x6*x7*x8 + 8) (x6*x7 + x6*x8 + x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_221  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_222  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_223 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_221   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_222   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_224  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_225  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_226 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_224   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_225   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_227 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_223 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_226 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_228  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_229  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_230 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_228   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_229   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_231  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_232  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_233 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_231   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_232   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_234 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_230 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_233 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_235 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (x7*x8 + x7 + x8) := by
    convert vertex_227 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (x7*x8 + x7 + x8) := by
    convert vertex_234 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_236  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_237  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_238 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_236   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_237   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_239  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_240  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_241 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_239   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_240   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_242 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_238 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_241 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_243  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_244  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_245 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_243   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_244   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_246  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_247  : (0 : ℝ) ≤ 2 := by
  norm_num

private theorem vertex_248 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-5) := by
    convert vertex_246   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-5) := by
    convert vertex_247   using 1 <;> ring
  have hc := affine_nonneg (7) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_249 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-4*x8 - 1) := by
    convert vertex_245 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-4*x8 - 1) := by
    convert vertex_248 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_250 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (-3*x7*x8 - x7 - x8) := by
    convert vertex_242 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (-3*x7*x8 - x7 - x8) := by
    convert vertex_249 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (-3*x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_251 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x6*x7*x8 + 8) - (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_235 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7*x8 + 8) + (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_250 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7*x8 + 8) (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_252 (x4 x5 x6 x7 x8 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7*x8 - x4*x5*x6*x7 - x4*x5*x6*x8 - x4*x5*x7*x8 - x4*x6*x7*x8 - x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x5*x6*x7*x8 + 8) - (-x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) := by
    convert vertex_220 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x5*x6*x7*x8 + 8) + (-x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) := by
    convert vertex_251 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x5*x6*x7*x8 + 8) (-x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_253 (x3 x4 x5 x6 x7 x8 : ℝ) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x3*x4*x5*x6*x7 - x3*x4*x5*x6*x8 - x3*x4*x5*x7*x8 - x3*x4*x6*x7*x8 - x3*x5*x6*x7*x8 - x4*x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x4*x5*x6*x7*x8 + 8) - (-x4*x5*x6*x7 - x4*x5*x6*x8 - x4*x5*x7*x8 - x4*x6*x7*x8 - x5*x6*x7*x8) := by
    convert vertex_189 x4 x5 x6 x7 x8 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x4*x5*x6*x7*x8 + 8) + (-x4*x5*x6*x7 - x4*x5*x6*x8 - x4*x5*x7*x8 - x4*x6*x7*x8 - x5*x6*x7*x8) := by
    convert vertex_252 x4 x5 x6 x7 x8 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x4*x5*x6*x7*x8 + 8) (-x4*x5*x6*x7 - x4*x5*x6*x8 - x4*x5*x7*x8 - x4*x6*x7*x8 - x5*x6*x7*x8) x3 hl_x3 hu_x3 hm hp
  convert hc using 1 <;> ring

private theorem vertex_254 (x2 x3 x4 x5 x6 x7 x8 : ℝ) (hl_x2 : -1 ≤ x2) (hu_x2 : x2 ≤ 1) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x2*x3*x4*x5*x6*x7*x8 - x2*x3*x4*x5*x6*x7 - x2*x3*x4*x5*x6*x8 - x2*x3*x4*x5*x7*x8 - x2*x3*x4*x6*x7*x8 - x2*x3*x5*x6*x7*x8 - x2*x4*x5*x6*x7*x8 - x3*x4*x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x3*x4*x5*x6*x7*x8 + 8) - (x3*x4*x5*x6*x7*x8 - x3*x4*x5*x6*x7 - x3*x4*x5*x6*x8 - x3*x4*x5*x7*x8 - x3*x4*x6*x7*x8 - x3*x5*x6*x7*x8 - x4*x5*x6*x7*x8) := by
    convert vertex_126 x3 x4 x5 x6 x7 x8 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x3*x4*x5*x6*x7*x8 + 8) + (x3*x4*x5*x6*x7*x8 - x3*x4*x5*x6*x7 - x3*x4*x5*x6*x8 - x3*x4*x5*x7*x8 - x3*x4*x6*x7*x8 - x3*x5*x6*x7*x8 - x4*x5*x6*x7*x8) := by
    convert vertex_253 x3 x4 x5 x6 x7 x8 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x3*x4*x5*x6*x7*x8 + 8) (x3*x4*x5*x6*x7*x8 - x3*x4*x5*x6*x7 - x3*x4*x5*x6*x8 - x3*x4*x5*x7*x8 - x3*x4*x6*x7*x8 - x3*x5*x6*x7*x8 - x4*x5*x6*x7*x8) x2 hl_x2 hu_x2 hm hp
  convert hc using 1 <;> ring

private theorem vertex_255  : (0 : ℝ) ≤ 14 := by
  norm_num

private theorem vertex_256  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_257 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-5) := by
    convert vertex_255   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-5) := by
    convert vertex_256   using 1 <;> ring
  have hc := affine_nonneg (9) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_258  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_259  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_260 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_258   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_259   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_261 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (4*x8 - 1) := by
    convert vertex_257 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (4*x8 - 1) := by
    convert vertex_260 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_262  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_263  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_264 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_262   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_263   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_265  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_266  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_267 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_265   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_266   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_268 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_264 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_267 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_269 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (-3*x7*x8 + x7 + x8) := by
    convert vertex_261 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (-3*x7*x8 + x7 + x8) := by
    convert vertex_268 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (-3*x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_270  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_271  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_272 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_270   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_271   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_273  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_274  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_275 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_273   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_274   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_276 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_272 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_275 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_277  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_278  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_279 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_277   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_278   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_280  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_281  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_282 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_280   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_281   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_283 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_279 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_282 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_284 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (x7*x8 - x7 - x8) := by
    convert vertex_276 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (x7*x8 - x7 - x8) := by
    convert vertex_283 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_285 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x6*x7*x8 + 8) - (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_269 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7*x8 + 8) + (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_284 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7*x8 + 8) (2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_286  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_287  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_288 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_286   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_287   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_289  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_290  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_291 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_289   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_290   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_292 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_288 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_291 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_293  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_294  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_295 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_293   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_294   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_296  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_297  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_298 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_296   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_297   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_299 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_295 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_298 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_300 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (x7*x8 - x7 - x8) := by
    convert vertex_292 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (x7*x8 - x7 - x8) := by
    convert vertex_299 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_301  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_302  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_303 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_301   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_302   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_304  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_305  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_306 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_304   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_305   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_307 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_303 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_306 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_308  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_309  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_310 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_308   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_309   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_311  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_312  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_313 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_311   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_312   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_314 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_310 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_313 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_315 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (x7*x8 + x7 + x8) := by
    convert vertex_307 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (x7*x8 + x7 + x8) := by
    convert vertex_314 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_316 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x6*x7*x8 + 8) - (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_300 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7*x8 + 8) + (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_315 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x6*x7*x8 + 8) (x6*x7 + x6*x8 + x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_317 (x4 x5 x6 x7 x8 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7*x8 + x4*x5*x6*x7 + x4*x5*x6*x8 + x4*x5*x7*x8 + x4*x6*x7*x8 + x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x5*x6*x7*x8 + 8) - (-x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) := by
    convert vertex_285 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x5*x6*x7*x8 + 8) + (-x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) := by
    convert vertex_316 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x5*x6*x7*x8 + 8) (-x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_318  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_319  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_320 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_318   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_319   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_321  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_322  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_323 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_321   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_322   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_324 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_320 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_323 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_325  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_326  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_327 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_325   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_326   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_328  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_329  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_330 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_328   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_329   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_331 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_327 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_330 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_332 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (x7*x8 - x7 - x8) := by
    convert vertex_324 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (x7*x8 - x7 - x8) := by
    convert vertex_331 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_333  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_334  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_335 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_333   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_334   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_336  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_337  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_338 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_336   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_337   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_339 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_335 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_338 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_340  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_341  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_342 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_340   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_341   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_343  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_344  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_345 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_343   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_344   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_346 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_342 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_345 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_347 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (x7*x8 + x7 + x8) := by
    convert vertex_339 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (x7*x8 + x7 + x8) := by
    convert vertex_346 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_348 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x6*x7*x8 + 8) - (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_332 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7*x8 + 8) + (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_347 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x6*x7*x8 + 8) (x6*x7 + x6*x8 + x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_349  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_350  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_351 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_349   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_350   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_352  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_353  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_354 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_352   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_353   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_355 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_351 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_354 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_356  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_357  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_358 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_356   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_357   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_359  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_360  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_361 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_359   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_360   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_362 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_358 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_361 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_363 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (x7*x8 + x7 + x8) := by
    convert vertex_355 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (x7*x8 + x7 + x8) := by
    convert vertex_362 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_364  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_365  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_366 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_364   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_365   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_367  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_368  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_369 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_367   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_368   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_370 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_366 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_369 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_371  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_372  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_373 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_371   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_372   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_374  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_375  : (0 : ℝ) ≤ 2 := by
  norm_num

private theorem vertex_376 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-5) := by
    convert vertex_374   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-5) := by
    convert vertex_375   using 1 <;> ring
  have hc := affine_nonneg (7) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_377 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-4*x8 - 1) := by
    convert vertex_373 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-4*x8 - 1) := by
    convert vertex_376 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_378 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (-3*x7*x8 - x7 - x8) := by
    convert vertex_370 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (-3*x7*x8 - x7 - x8) := by
    convert vertex_377 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (-3*x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_379 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x6*x7*x8 + 8) - (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_363 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7*x8 + 8) + (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_378 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7*x8 + 8) (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_380 (x4 x5 x6 x7 x8 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7*x8 - x4*x5*x6*x7 - x4*x5*x6*x8 - x4*x5*x7*x8 - x4*x6*x7*x8 - x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x5*x6*x7*x8 + 8) - (-x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) := by
    convert vertex_348 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x5*x6*x7*x8 + 8) + (-x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) := by
    convert vertex_379 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x5*x6*x7*x8 + 8) (-x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_381 (x3 x4 x5 x6 x7 x8 : ℝ) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x3*x4*x5*x6*x7 - x3*x4*x5*x6*x8 - x3*x4*x5*x7*x8 - x3*x4*x6*x7*x8 - x3*x5*x6*x7*x8 - x4*x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x4*x5*x6*x7*x8 + 8) - (-x4*x5*x6*x7 - x4*x5*x6*x8 - x4*x5*x7*x8 - x4*x6*x7*x8 - x5*x6*x7*x8) := by
    convert vertex_317 x4 x5 x6 x7 x8 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x4*x5*x6*x7*x8 + 8) + (-x4*x5*x6*x7 - x4*x5*x6*x8 - x4*x5*x7*x8 - x4*x6*x7*x8 - x5*x6*x7*x8) := by
    convert vertex_380 x4 x5 x6 x7 x8 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x4*x5*x6*x7*x8 + 8) (-x4*x5*x6*x7 - x4*x5*x6*x8 - x4*x5*x7*x8 - x4*x6*x7*x8 - x5*x6*x7*x8) x3 hl_x3 hu_x3 hm hp
  convert hc using 1 <;> ring

private theorem vertex_382  : (0 : ℝ) ≤ 4 := by
  norm_num

private theorem vertex_383  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_384 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 7 := by
  have hm : (0 : ℝ) ≤ (7) - (3) := by
    convert vertex_382   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (3) := by
    convert vertex_383   using 1 <;> ring
  have hc := affine_nonneg (7) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_385  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_386  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_387 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_385   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_386   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_388 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (1 - 2*x8) := by
    convert vertex_384 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (1 - 2*x8) := by
    convert vertex_387 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (1 - 2*x8) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_389  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_390  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_391 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_389   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_390   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_392  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_393  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_394 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_392   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_393   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_395 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_391 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_394 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_396 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (x7*x8 - x7 - x8) := by
    convert vertex_388 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (x7*x8 - x7 - x8) := by
    convert vertex_395 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_397  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_398  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_399 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_397   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_398   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_400  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_401  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_402 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_400   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_401   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_403 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_399 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_402 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_404  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_405  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_406 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_404   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_405   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_407  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_408  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_409 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_407   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_408   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_410 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_406 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_409 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_411 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (x7*x8 + x7 + x8) := by
    convert vertex_403 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (x7*x8 + x7 + x8) := by
    convert vertex_410 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_412 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x6*x7*x8 + 8) - (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_396 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7*x8 + 8) + (x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_411 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x6*x7*x8 + 8) (x6*x7 + x6*x8 + x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_413  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_414  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_415 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_413   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_414   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_416  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_417  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_418 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_416   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_417   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_419 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_415 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_418 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_420  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_421  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_422 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_420   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_421   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_423  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_424  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_425 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_423   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_424   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_426 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_422 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_425 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_427 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (x7*x8 + x7 + x8) := by
    convert vertex_419 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (x7*x8 + x7 + x8) := by
    convert vertex_426 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_428  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_429  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_430 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_428   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_429   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_431  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_432  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_433 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_431   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_432   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_434 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_430 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_433 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_435  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_436  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_437 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_435   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_436   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_438  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_439  : (0 : ℝ) ≤ 2 := by
  norm_num

private theorem vertex_440 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-5) := by
    convert vertex_438   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-5) := by
    convert vertex_439   using 1 <;> ring
  have hc := affine_nonneg (7) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_441 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-4*x8 - 1) := by
    convert vertex_437 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-4*x8 - 1) := by
    convert vertex_440 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_442 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (-3*x7*x8 - x7 - x8) := by
    convert vertex_434 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (-3*x7*x8 - x7 - x8) := by
    convert vertex_441 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (-3*x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_443 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x6*x7*x8 + 8) - (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_427 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7*x8 + 8) + (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_442 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7*x8 + 8) (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_444 (x4 x5 x6 x7 x8 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x4*x5*x6*x7*x8 - x4*x5*x6*x7 - x4*x5*x6*x8 - x4*x5*x7*x8 - x4*x6*x7*x8 - x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x5*x6*x7*x8 + 8) - (-x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) := by
    convert vertex_412 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x5*x6*x7*x8 + 8) + (-x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) := by
    convert vertex_443 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x5*x6*x7*x8 + 8) (-x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_445  : (0 : ℝ) ≤ 10 := by
  norm_num

private theorem vertex_446  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_447 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 9 - x8 := by
  have hm : (0 : ℝ) ≤ (9) - (-1) := by
    convert vertex_445   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (-1) := by
    convert vertex_446   using 1 <;> ring
  have hc := affine_nonneg (9) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_448  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_449  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_450 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_448   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_449   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_451 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-1) := by
    convert vertex_447 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-1) := by
    convert vertex_450 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_452  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_453  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_454 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_452   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_453   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_455  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_456  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_457 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_455   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_456   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_458 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_454 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_457 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_459 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (x7*x8 + x7 + x8) := by
    convert vertex_451 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (x7*x8 + x7 + x8) := by
    convert vertex_458 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_460  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_461  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_462 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_460   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_461   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_463  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_464  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_465 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_463   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_464   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_466 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_462 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_465 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_467  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_468  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_469 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_467   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_468   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_470  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_471  : (0 : ℝ) ≤ 2 := by
  norm_num

private theorem vertex_472 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-5) := by
    convert vertex_470   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-5) := by
    convert vertex_471   using 1 <;> ring
  have hc := affine_nonneg (7) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_473 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-4*x8 - 1) := by
    convert vertex_469 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-4*x8 - 1) := by
    convert vertex_472 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_474 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (-3*x7*x8 - x7 - x8) := by
    convert vertex_466 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (-3*x7*x8 - x7 - x8) := by
    convert vertex_473 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (-3*x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_475 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -2*x5*x6*x7*x8 - x5*x6*x7 - x5*x6*x8 - x5*x7*x8 - x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x6*x7*x8 + 8) - (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_459 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x6*x7*x8 + 8) + (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) := by
    convert vertex_474 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x6*x7*x8 + 8) (-2*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_476  : (0 : ℝ) ≤ 8 := by
  norm_num

private theorem vertex_477  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_478 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-1) := by
    convert vertex_476   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-1) := by
    convert vertex_477   using 1 <;> ring
  have hc := affine_nonneg (7) (-1) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_479  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_480  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_481 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_479   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_480   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_482 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (2*x8 + 1) := by
    convert vertex_478 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (2*x8 + 1) := by
    convert vertex_481 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (2*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_483  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_484  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_485 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_483   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_484   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_486  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_487  : (0 : ℝ) ≤ 2 := by
  norm_num

private theorem vertex_488 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-5) := by
    convert vertex_486   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-5) := by
    convert vertex_487   using 1 <;> ring
  have hc := affine_nonneg (7) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_489 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-4*x8 - 1) := by
    convert vertex_485 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-4*x8 - 1) := by
    convert vertex_488 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_490 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -3*x6*x7*x8 - x6*x7 - x6*x8 - x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (-x7*x8 + 8) - (-3*x7*x8 - x7 - x8) := by
    convert vertex_482 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (-x7*x8 + 8) + (-3*x7*x8 - x7 - x8) := by
    convert vertex_489 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (-x7*x8 + 8) (-3*x7*x8 - x7 - x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_491  : (0 : ℝ) ≤ 6 := by
  norm_num

private theorem vertex_492  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_493 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (3) := by
    convert vertex_491   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (3) := by
    convert vertex_492   using 1 <;> ring
  have hc := affine_nonneg (9) (3) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_494  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_495  : (0 : ℝ) ≤ 2 := by
  norm_num

private theorem vertex_496 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-5) := by
    convert vertex_494   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-5) := by
    convert vertex_495   using 1 <;> ring
  have hc := affine_nonneg (7) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_497 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ -4*x7*x8 - x7 - x8 + 8 := by
  have hm : (0 : ℝ) ≤ (8 - x8) - (-4*x8 - 1) := by
    convert vertex_493 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (8 - x8) + (-4*x8 - 1) := by
    convert vertex_496 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (8 - x8) (-4*x8 - 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_498  : (0 : ℝ) ≤ 12 := by
  norm_num

private theorem vertex_499  : (0 : ℝ) ≤ 2 := by
  norm_num

private theorem vertex_500 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7 - 5*x8 := by
  have hm : (0 : ℝ) ≤ (7) - (-5) := by
    convert vertex_498   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (7) + (-5) := by
    convert vertex_499   using 1 <;> ring
  have hc := affine_nonneg (7) (-5) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_501  : (0 : ℝ) ≤ 2 := by
  norm_num

private theorem vertex_502  : (0 : ℝ) ≤ 16 := by
  norm_num

private theorem vertex_503 (x8 : ℝ) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 7*x8 + 9 := by
  have hm : (0 : ℝ) ≤ (9) - (7) := by
    convert vertex_501   using 1 <;> ring
  have hp : (0 : ℝ) ≤ (9) + (7) := by
    convert vertex_502   using 1 <;> ring
  have hc := affine_nonneg (9) (7) x8 hl_x8 hu_x8 hm hp
  convert hc using 1 <;> ring

private theorem vertex_504 (x7 x8 : ℝ) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 6*x7*x8 + x7 + x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x8 + 8) - (6*x8 + 1) := by
    convert vertex_500 x8 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x8 + 8) + (6*x8 + 1) := by
    convert vertex_503 x8 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x8 + 8) (6*x8 + 1) x7 hl_x7 hu_x7 hm hp
  convert hc using 1 <;> ring

private theorem vertex_505 (x6 x7 x8 : ℝ) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 5*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x7*x8 + 8) - (5*x7*x8 + x7 + x8) := by
    convert vertex_497 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x7*x8 + 8) + (5*x7*x8 + x7 + x8) := by
    convert vertex_504 x7 x8 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x7*x8 + 8) (5*x7*x8 + x7 + x8) x6 hl_x6 hu_x6 hm hp
  convert hc using 1 <;> ring

private theorem vertex_506 (x5 x6 x7 x8 : ℝ) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 4*x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x6*x7*x8 + 8) - (4*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_490 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x6*x7*x8 + 8) + (4*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8) := by
    convert vertex_505 x6 x7 x8 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x6*x7*x8 + 8) (4*x6*x7*x8 + x6*x7 + x6*x8 + x7*x8) x5 hl_x5 hu_x5 hm hp
  convert hc using 1 <;> ring

private theorem vertex_507 (x4 x5 x6 x7 x8 : ℝ) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 3*x4*x5*x6*x7*x8 + x4*x5*x6*x7 + x4*x5*x6*x8 + x4*x5*x7*x8 + x4*x6*x7*x8 + x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x5*x6*x7*x8 + 8) - (3*x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) := by
    convert vertex_475 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x5*x6*x7*x8 + 8) + (3*x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) := by
    convert vertex_506 x5 x6 x7 x8 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x5*x6*x7*x8 + 8) (3*x5*x6*x7*x8 + x5*x6*x7 + x5*x6*x8 + x5*x7*x8 + x6*x7*x8) x4 hl_x4 hu_x4 hm hp
  convert hc using 1 <;> ring

private theorem vertex_508 (x3 x4 x5 x6 x7 x8 : ℝ) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ 2*x3*x4*x5*x6*x7*x8 + x3*x4*x5*x6*x7 + x3*x4*x5*x6*x8 + x3*x4*x5*x7*x8 + x3*x4*x6*x7*x8 + x3*x5*x6*x7*x8 + x4*x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x4*x5*x6*x7*x8 + 8) - (2*x4*x5*x6*x7*x8 + x4*x5*x6*x7 + x4*x5*x6*x8 + x4*x5*x7*x8 + x4*x6*x7*x8 + x5*x6*x7*x8) := by
    convert vertex_444 x4 x5 x6 x7 x8 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x4*x5*x6*x7*x8 + 8) + (2*x4*x5*x6*x7*x8 + x4*x5*x6*x7 + x4*x5*x6*x8 + x4*x5*x7*x8 + x4*x6*x7*x8 + x5*x6*x7*x8) := by
    convert vertex_507 x4 x5 x6 x7 x8 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x4*x5*x6*x7*x8 + 8) (2*x4*x5*x6*x7*x8 + x4*x5*x6*x7 + x4*x5*x6*x8 + x4*x5*x7*x8 + x4*x6*x7*x8 + x5*x6*x7*x8) x3 hl_x3 hu_x3 hm hp
  convert hc using 1 <;> ring

private theorem vertex_509 (x2 x3 x4 x5 x6 x7 x8 : ℝ) (hl_x2 : -1 ≤ x2) (hu_x2 : x2 ≤ 1) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x2*x3*x4*x5*x6*x7*x8 + x2*x3*x4*x5*x6*x7 + x2*x3*x4*x5*x6*x8 + x2*x3*x4*x5*x7*x8 + x2*x3*x4*x6*x7*x8 + x2*x3*x5*x6*x7*x8 + x2*x4*x5*x6*x7*x8 + x3*x4*x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x3*x4*x5*x6*x7*x8 + 8) - (x3*x4*x5*x6*x7*x8 + x3*x4*x5*x6*x7 + x3*x4*x5*x6*x8 + x3*x4*x5*x7*x8 + x3*x4*x6*x7*x8 + x3*x5*x6*x7*x8 + x4*x5*x6*x7*x8) := by
    convert vertex_381 x3 x4 x5 x6 x7 x8 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x3*x4*x5*x6*x7*x8 + 8) + (x3*x4*x5*x6*x7*x8 + x3*x4*x5*x6*x7 + x3*x4*x5*x6*x8 + x3*x4*x5*x7*x8 + x3*x4*x6*x7*x8 + x3*x5*x6*x7*x8 + x4*x5*x6*x7*x8) := by
    convert vertex_508 x3 x4 x5 x6 x7 x8 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x3*x4*x5*x6*x7*x8 + 8) (x3*x4*x5*x6*x7*x8 + x3*x4*x5*x6*x7 + x3*x4*x5*x6*x8 + x3*x4*x5*x7*x8 + x3*x4*x6*x7*x8 + x3*x5*x6*x7*x8 + x4*x5*x6*x7*x8) x2 hl_x2 hu_x2 hm hp
  convert hc using 1 <;> ring

private theorem vertex_510 (x1 x2 x3 x4 x5 x6 x7 x8 : ℝ) (hl_x1 : -1 ≤ x1) (hu_x1 : x1 ≤ 1) (hl_x2 : -1 ≤ x2) (hu_x2 : x2 ≤ 1) (hl_x3 : -1 ≤ x3) (hu_x3 : x3 ≤ 1) (hl_x4 : -1 ≤ x4) (hu_x4 : x4 ≤ 1) (hl_x5 : -1 ≤ x5) (hu_x5 : x5 ≤ 1) (hl_x6 : -1 ≤ x6) (hu_x6 : x6 ≤ 1) (hl_x7 : -1 ≤ x7) (hu_x7 : x7 ≤ 1) (hl_x8 : -1 ≤ x8) (hu_x8 : x8 ≤ 1) : (0 : ℝ) ≤ x1*x2*x3*x4*x5*x6*x7 + x1*x2*x3*x4*x5*x6*x8 + x1*x2*x3*x4*x5*x7*x8 + x1*x2*x3*x4*x6*x7*x8 + x1*x2*x3*x5*x6*x7*x8 + x1*x2*x4*x5*x6*x7*x8 + x1*x3*x4*x5*x6*x7*x8 + x2*x3*x4*x5*x6*x7*x8 + 8 := by
  have hm : (0 : ℝ) ≤ (x2*x3*x4*x5*x6*x7*x8 + 8) - (x2*x3*x4*x5*x6*x7 + x2*x3*x4*x5*x6*x8 + x2*x3*x4*x5*x7*x8 + x2*x3*x4*x6*x7*x8 + x2*x3*x5*x6*x7*x8 + x2*x4*x5*x6*x7*x8 + x3*x4*x5*x6*x7*x8) := by
    convert vertex_254 x2 x3 x4 x5 x6 x7 x8 hl_x2 hu_x2 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hp : (0 : ℝ) ≤ (x2*x3*x4*x5*x6*x7*x8 + 8) + (x2*x3*x4*x5*x6*x7 + x2*x3*x4*x5*x6*x8 + x2*x3*x4*x5*x7*x8 + x2*x3*x4*x6*x7*x8 + x2*x3*x5*x6*x7*x8 + x2*x4*x5*x6*x7*x8 + x3*x4*x5*x6*x7*x8) := by
    convert vertex_509 x2 x3 x4 x5 x6 x7 x8 hl_x2 hu_x2 hl_x3 hu_x3 hl_x4 hu_x4 hl_x5 hu_x5 hl_x6 hu_x6 hl_x7 hu_x7 hl_x8 hu_x8 using 1 <;> ring
  have hc := affine_nonneg (x2*x3*x4*x5*x6*x7*x8 + 8) (x2*x3*x4*x5*x6*x7 + x2*x3*x4*x5*x6*x8 + x2*x3*x4*x5*x7*x8 + x2*x3*x4*x6*x7*x8 + x2*x3*x5*x6*x7*x8 + x2*x4*x5*x6*x7*x8 + x3*x4*x5*x6*x7*x8) x1 hl_x1 hu_x1 hm hp
  convert hc using 1 <;> ring
theorem result (x1 x2 x3 x4 x5 x6 x7 x8 : ℝ) (hl0 : (-1 : ℝ) ≤ x1) (hu0 : x1 ≤ (1 : ℝ)) (hl1 : (-1 : ℝ) ≤ x2) (hu1 : x2 ≤ (1 : ℝ)) (hl2 : (-1 : ℝ) ≤ x3) (hu2 : x3 ≤ (1 : ℝ)) (hl3 : (-1 : ℝ) ≤ x4) (hu3 : x4 ≤ (1 : ℝ)) (hl4 : (-1 : ℝ) ≤ x5) (hu4 : x5 ≤ (1 : ℝ)) (hl5 : (-1 : ℝ) ≤ x6) (hu5 : x6 ≤ (1 : ℝ)) (hl6 : (-1 : ℝ) ≤ x7) (hu6 : x7 ≤ (1 : ℝ)) (hl7 : (-1 : ℝ) ≤ x8) (hu7 : x8 ≤ (1 : ℝ)) : (0 : ℝ) ≤ 8 + x1*x2*x3*x4*x5*x6*x7 + x1*x2*x3*x4*x5*x6*x8 + x1*x2*x3*x4*x5*x7*x8 + x1*x2*x3*x4*x6*x7*x8 + x1*x2*x3*x5*x6*x7*x8 + x1*x2*x4*x5*x6*x7*x8 + x1*x3*x4*x5*x6*x7*x8 + x2*x3*x4*x5*x6*x7*x8 := by
  convert vertex_510 x1 x2 x3 x4 x5 x6 x7 x8 hl0 hu0 hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4 hl5 hu5 hl6 hu6 hl7 hu7 using 1 <;> ring



set_option linter.style.header false
set_option linter.unusedVariables false

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 38
id: A18
name: Cyc 8
reference: An efficient algorithm for range computation of polynomials using the Bernstein form
reference_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: x1*x2*x3*x4*x5*x6*x7 + x2*x3*x4*x5*x6*x7*x8 + x1*x3*x4*x5*x6*x7*x8 + x1*x2*x4*x5*x6*x7*x8 + x1*x2*x3*x5*x6*x7*x8 + x1*x2*x3*x4*x6*x7*x8 + x1*x2*x3*x4*x5*x7*x8 + x1*x2*x3*x4*x5*x6*x8 + 8
source_location: Table 1 Ex 18; Appendix A Problem 18

-/
theorem box_benchmark_38_a18_cyc_8 :
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
        0 <= 8 + x1*x2*x3*x4*x5*x6*x7 + x1*x2*x3*x4*x5*x6*x8 + x1*x2*x3*x4*x5*x7*x8 + x1*x2*x3*x4*x6*x7*x8 + x1*x2*x3*x5*x6*x7*x8 + x1*x2*x4*x5*x6*x7*x8 + x1*x3*x4*x5*x6*x7*x8 + x2*x3*x4*x5*x6*x7*x8 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4, hl5, hu5, hl6, hu6, hl7, hu7⟩
  have htranslated := @result x1 x2 x3 x4 x5 x6 x7 x8 (by convert hl0 using 1 <;> norm_num) (by convert hu0 using 1 <;> norm_num) (by convert hl1 using 1 <;> norm_num) (by convert hu1 using 1 <;> norm_num) (by convert hl2 using 1 <;> norm_num) (by convert hu2 using 1 <;> norm_num) (by convert hl3 using 1 <;> norm_num) (by convert hu3 using 1 <;> norm_num) (by convert hl4 using 1 <;> norm_num) (by convert hu4 using 1 <;> norm_num) (by convert hl5 using 1 <;> norm_num) (by convert hu5 using 1 <;> norm_num) (by convert hl6 using 1 <;> norm_num) (by convert hu6 using 1 <;> norm_num) (by convert hl7 using 1 <;> norm_num) (by convert hu7 using 1 <;> norm_num)
  convert htranslated using 1 <;> ring

end Leanpro.BoxJsonlWithSources
