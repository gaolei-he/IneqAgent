import Mathlib

set_option linter.style.header false

def deltaX4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6
  + x1 * (-x1 + x2 + x3 - x4 + x5 + x6)


set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace Certificate_ineq4559601669b

private theorem blend1 (t a b : ℝ) (ht : 0 ≤ t) (hc : 0 ≤ 1-t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a*(1-t) + b*t := by
  exact add_nonneg (mul_nonneg ha hc) (mul_nonneg hb ht)

private theorem blend2 (t a b c : ℝ) (ht : 0 ≤ t) (hc : 0 ≤ 1-t)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : 0 ≤ c) :
    0 ≤ a*(1-t)^2 + 2*b*t*(1-t) + c*t^2 := by
  have hm : 0 ≤ 2*b*t*(1-t) := by positivity
  exact add_nonneg (add_nonneg (mul_nonneg ha (sq_nonneg (1-t))) hm)
    (mul_nonneg hh (sq_nonneg t))

private theorem node_0  : (0 : ℝ) ≤ (24480799/1000000) := by
  norm_num

private theorem node_1  : (0 : ℝ) ≤ (15079199/1000000) := by
  norm_num

private theorem node_2 (t4 : ℝ) (ht4 : 0 ≤ t4) (hct4 : 0 ≤ 1-t4) : (0 : ℝ) ≤ (24480799/1000000 - 5876*t4/625) := by
  have hp0 : (0 : ℝ) ≤ (24480799/1000000) := node_0  
  have hp1 : (0 : ℝ) ≤ (15079199/1000000) := node_1  
  have hb := blend1 t4 (24480799/1000000) (15079199/1000000) ht4 hct4 hp0 hp1
  convert hb using 1 <;> ring

private theorem node_3  : (0 : ℝ) ≤ (5677599/1000000) := by
  norm_num

private theorem node_4 (t4 : ℝ) (ht4 : 0 ≤ t4) (hct4 : 0 ≤ 1-t4) : (0 : ℝ) ≤ (15079199/1000000 - 5876*t4/625) := by
  have hp0 : (0 : ℝ) ≤ (15079199/1000000) := node_1  
  have hp1 : (0 : ℝ) ≤ (5677599/1000000) := node_3  
  have hb := blend1 t4 (15079199/1000000) (5677599/1000000) ht4 hct4 hp0 hp1
  convert hb using 1 <;> ring

private theorem node_5 (t2 t4 : ℝ) (ht2 : 0 ≤ t2) (hct2 : 0 ≤ 1-t2) (ht4 : 0 ≤ t4) (hct4 : 0 ≤ 1-t4) : (0 : ℝ) ≤ (-5876*t2/625 - 5876*t4/625 + 24480799/1000000) := by
  have hp0 : (0 : ℝ) ≤ (24480799/1000000 - 5876*t4/625) := node_2 t4 ht4 hct4
  have hp1 : (0 : ℝ) ≤ (15079199/1000000 - 5876*t4/625) := node_4 t4 ht4 hct4
  have hb := blend1 t2 (24480799/1000000 - 5876*t4/625) (15079199/1000000 - 5876*t4/625) ht2 hct2 hp0 hp1
  convert hb using 1 <;> ring

private theorem node_6  : (0 : ℝ) ≤ (909351451/25000000) := by
  norm_num

private theorem node_7  : (0 : ℝ) ≤ (605256699/25000000) := by
  norm_num

private theorem node_8 (t4 : ℝ) (ht4 : 0 ≤ t4) (hct4 : 0 ≤ 1-t4) : (0 : ℝ) ≤ (909351451/25000000 - 9502961*t4/781250) := by
  have hp0 : (0 : ℝ) ≤ (909351451/25000000) := node_6  
  have hp1 : (0 : ℝ) ≤ (605256699/25000000) := node_7  
  have hb := blend1 t4 (909351451/25000000) (605256699/25000000) ht4 hct4 hp0 hp1
  convert hb using 1 <;> ring

private theorem node_9  : (0 : ℝ) ≤ (301161947/25000000) := by
  norm_num

private theorem node_10 (t4 : ℝ) (ht4 : 0 ≤ t4) (hct4 : 0 ≤ 1-t4) : (0 : ℝ) ≤ (605256699/25000000 - 9502961*t4/781250) := by
  have hp0 : (0 : ℝ) ≤ (605256699/25000000) := node_7  
  have hp1 : (0 : ℝ) ≤ (301161947/25000000) := node_9  
  have hb := blend1 t4 (605256699/25000000) (301161947/25000000) ht4 hct4 hp0 hp1
  convert hb using 1 <;> ring

private theorem node_11 (t2 t4 : ℝ) (ht2 : 0 ≤ t2) (hct2 : 0 ≤ 1-t2) (ht4 : 0 ≤ t4) (hct4 : 0 ≤ 1-t4) : (0 : ℝ) ≤ (-9502961*t2/781250 - 9502961*t4/781250 + 909351451/25000000) := by
  have hp0 : (0 : ℝ) ≤ (909351451/25000000 - 9502961*t4/781250) := node_8 t4 ht4 hct4
  have hp1 : (0 : ℝ) ≤ (605256699/25000000 - 9502961*t4/781250) := node_10 t4 ht4 hct4
  have hb := blend1 t2 (909351451/25000000 - 9502961*t4/781250) (605256699/25000000 - 9502961*t4/781250) ht2 hct2 hp0 hp1
  convert hb using 1 <;> ring

private theorem node_12  : (0 : ℝ) ≤ (1344792431/25000000) := by
  norm_num

private theorem node_13  : (0 : ℝ) ≤ (971642927/25000000) := by
  norm_num

private theorem node_14 (t4 : ℝ) (ht4 : 0 ≤ t4) (hct4 : 0 ≤ 1-t4) : (0 : ℝ) ≤ (1344792431/25000000 - 5830461*t4/390625) := by
  have hp0 : (0 : ℝ) ≤ (1344792431/25000000) := node_12  
  have hp1 : (0 : ℝ) ≤ (971642927/25000000) := node_13  
  have hb := blend1 t4 (1344792431/25000000) (971642927/25000000) ht4 hct4 hp0 hp1
  convert hb using 1 <;> ring

private theorem node_15  : (0 : ℝ) ≤ (598493423/25000000) := by
  norm_num

private theorem node_16 (t4 : ℝ) (ht4 : 0 ≤ t4) (hct4 : 0 ≤ 1-t4) : (0 : ℝ) ≤ (971642927/25000000 - 5830461*t4/390625) := by
  have hp0 : (0 : ℝ) ≤ (971642927/25000000) := node_13  
  have hp1 : (0 : ℝ) ≤ (598493423/25000000) := node_15  
  have hb := blend1 t4 (971642927/25000000) (598493423/25000000) ht4 hct4 hp0 hp1
  convert hb using 1 <;> ring

private theorem node_17 (t2 t4 : ℝ) (ht2 : 0 ≤ t2) (hct2 : 0 ≤ 1-t2) (ht4 : 0 ≤ t4) (hct4 : 0 ≤ 1-t4) : (0 : ℝ) ≤ (-5830461*t2/390625 - 5830461*t4/390625 + 1344792431/25000000) := by
  have hp0 : (0 : ℝ) ≤ (1344792431/25000000 - 5830461*t4/390625) := node_14 t4 ht4 hct4
  have hp1 : (0 : ℝ) ≤ (971642927/25000000 - 5830461*t4/390625) := node_16 t4 ht4 hct4
  have hb := blend1 t2 (1344792431/25000000 - 5830461*t4/390625) (971642927/25000000 - 5830461*t4/390625) ht2 hct2 hp0 hp1
  convert hb using 1 <;> ring

private theorem node_18 (t0 t2 t4 : ℝ) (ht0 : 0 ≤ t0) (hct0 : 0 ≤ 1-t0) (ht2 : 0 ≤ t2) (hct2 : 0 ≤ 1-t2) (ht4 : 0 ≤ t4) (hct4 : 0 ≤ 1-t4) : (0 : ℝ) ≤ (2157961*t0^2/390625 - 2157961*t0*t2/390625 - 2157961*t0*t4/390625 + 74332869*t0/3125000 - 5876*t2/625 - 5876*t4/625 + 24480799/1000000) := by
  have hp0 : (0 : ℝ) ≤ (-5876*t2/625 - 5876*t4/625 + 24480799/1000000) := node_5 t2 t4 ht2 hct2 ht4 hct4
  have hp1 : (0 : ℝ) ≤ (-9502961*t2/781250 - 9502961*t4/781250 + 909351451/25000000) := node_11 t2 t4 ht2 hct2 ht4 hct4
  have hp2 : (0 : ℝ) ≤ (-5830461*t2/390625 - 5830461*t4/390625 + 1344792431/25000000) := node_17 t2 t4 ht2 hct2 ht4 hct4
  have hb := blend2 t0 (-5876*t2/625 - 5876*t4/625 + 24480799/1000000) (-9502961*t2/781250 - 9502961*t4/781250 + 909351451/25000000) (-5830461*t2/390625 - 5830461*t4/390625 + 1344792431/25000000) ht0 hct0 hp0 hp1 hp2
  convert hb using 1 <;> ring

end Certificate_ineq4559601669b

theorem ineq4559601669b :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      4.0 ≤ x1 ∧ x1 ≤ 6.3504 ∧
      4.0 ≤ x2 ∧ x2 ≤ 4.0 ∧
      4.0 ≤ x3 ∧ x3 ≤ 6.3504 ∧
      3.01 * 3.01 ≤ x4 ∧ x4 ≤ 3.01 * 3.01 ∧
      4.0 ≤ x5 ∧ x5 ≤ 6.3504 ∧
      4.0 ≤ x6 ∧ x6 ≤ 4.0 →
        deltaX4 x1 x2 x3 x4 x5 x6 < 0 := by
  intro x1 x2 x3 x4 x5 x6 ⟨hl0, hu0, hl1, hu1, hl2, hu2, hl3, hu3, hl4, hu4, hl5, hu5⟩
  norm_num at hl0 hu0 hl1 hu1 hl2 hu2 hl3 hu3 hl4 hu4 hl5 hu5
  let t0 : ℝ := (x1 - (4)) / (1469/625)
  have ht0 : 0 ≤ t0 := by dsimp [t0]; positivity
  have htu0 : t0 ≤ 1 := by dsimp [t0]; apply (div_le_one (by norm_num)).2; linarith only [hu0]
  have hct0 : 0 ≤ 1-t0 := sub_nonneg.mpr htu0
  have hv0 : x1 = (4) + (1469/625)*t0 := by dsimp [t0]; ring
  have hv1 : x2 = (4 : ℝ) := by linarith only [hl1, hu1]
  let t2 : ℝ := (x3 - (4)) / (1469/625)
  have ht2 : 0 ≤ t2 := by dsimp [t2]; positivity
  have htu2 : t2 ≤ 1 := by dsimp [t2]; apply (div_le_one (by norm_num)).2; linarith only [hu2]
  have hct2 : 0 ≤ 1-t2 := sub_nonneg.mpr htu2
  have hv2 : x3 = (4) + (1469/625)*t2 := by dsimp [t2]; ring
  have hv3 : x4 = (90601/10000 : ℝ) := by linarith only [hl3, hu3]
  let t4 : ℝ := (x5 - (4)) / (1469/625)
  have ht4 : 0 ≤ t4 := by dsimp [t4]; positivity
  have htu4 : t4 ≤ 1 := by dsimp [t4]; apply (div_le_one (by norm_num)).2; linarith only [hu4]
  have hct4 : 0 ≤ 1-t4 := sub_nonneg.mpr htu4
  have hv4 : x5 = (4) + (1469/625)*t4 := by dsimp [t4]; ring
  have hv5 : x6 = (4 : ℝ) := by linarith only [hl5, hu5]
  have hb := Certificate_ineq4559601669b.node_18 t0 t2 t4 ht0 hct0 ht2 hct2 ht4 hct4
  have hid : (x1^2 - x1*x2 - x1*x3 + 2*x1*x4 - x1*x5 - x1*x6 + x2*x3 - x2*x5 - x3*x6 + x5*x6 - 1/1000000) = (2157961*t0^2/390625 - 2157961*t0*t2/390625 - 2157961*t0*t4/390625 + 74332869*t0/3125000 - 5876*t2/625 - 5876*t4/625 + 24480799/1000000) := by
    rw [hv0, hv1, hv2, hv3, hv4, hv5]
    ring
  have hg : (0 : ℝ) ≤ (x1^2 - x1*x2 - x1*x3 + 2*x1*x4 - x1*x5 - x1*x6 + x2*x3 - x2*x5 - x3*x6 + x5*x6 - 1/1000000) := by rw [hid]; exact hb
  unfold deltaX4
  nlinarith only [hg]

#print axioms ineq4559601669b
