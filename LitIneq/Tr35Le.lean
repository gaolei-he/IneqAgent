import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

def tr (phi : ℝ) : ℝ :=
  9.8 * Real.tan phi / (250 * 0.514)

theorem tr_35_le :
    3 * Real.pi / 180 ≤ tr (35 * Real.pi / 180) := by
  have h_inv_sqrt_lt : (1 : ℝ) / √3 < (1287 : ℝ) / 2227 := by
    have hroot_pos : 0 < √(3 : ℝ) := Real.sqrt_pos_of_pos (by norm_num)
    have hrat_pos : 0 < (2227 : ℝ) / 1287 := by norm_num
    have hsq : ((2227 : ℝ) / 1287) ^ 2 < (√(3 : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have hroot : (2227 : ℝ) / 1287 < √(3 : ℝ) := by
      rw [← sq_lt_sq₀ hrat_pos.le hroot_pos.le]
      exact hsq
    have hinv : (√(3 : ℝ))⁻¹ < ((2227 : ℝ) / 1287)⁻¹ := by
      exact (inv_lt_inv₀ hroot_pos hrat_pos).2 hroot
    norm_num [one_div] at hinv ⊢
    exact hinv
  have h_three_arctan :
      3 * Real.arctan ((3 : ℝ) / 17) = Real.arctan ((1287 : ℝ) / 2227) := by
    have h_two_arctan :
        2 * Real.arctan ((3 : ℝ) / 17) = Real.arctan ((51 : ℝ) / 140) := by
      rw [Real.two_mul_arctan] <;> norm_num
    calc
      3 * Real.arctan ((3 : ℝ) / 17)
          = 2 * Real.arctan ((3 : ℝ) / 17) + Real.arctan ((3 : ℝ) / 17) := by ring
      _ = Real.arctan ((51 : ℝ) / 140) + Real.arctan ((3 : ℝ) / 17) := by
        rw [h_two_arctan]
      _ = Real.arctan
          ((((51 : ℝ) / 140) + (3 / 17)) / (1 - ((51 / 140) * (3 / 17)))) := by
        rw [Real.arctan_add]
        norm_num
      _ = Real.arctan ((1287 : ℝ) / 2227) := by norm_num
  have h_pi_eighteen_lt_arctan : Real.pi / 18 < Real.arctan ((3 : ℝ) / 17) := by
    have h_pi_six_lt : Real.pi / 6 < 3 * Real.arctan ((3 : ℝ) / 17) := by
      calc
        Real.pi / 6 = Real.arctan ((1 : ℝ) / √3) := by
          rw [one_div]
          exact (Real.arctan_inv_sqrt_three).symm
        _ < Real.arctan ((1287 : ℝ) / 2227) := Real.arctan_strictMono h_inv_sqrt_lt
        _ = 3 * Real.arctan ((3 : ℝ) / 17) := h_three_arctan.symm
    linarith
  have h_arctan_sum :
      Real.arctan ((7 : ℝ) / 10) + Real.arctan ((3 : ℝ) / 17) = Real.pi / 4 := by
    calc
      Real.arctan ((7 : ℝ) / 10) + Real.arctan ((3 : ℝ) / 17)
          = Real.arctan ((((7 : ℝ) / 10) + (3 / 17)) / (1 - ((7 / 10) * (3 / 17)))) := by
        rw [Real.arctan_add]
        norm_num
      _ = Real.arctan (1 : ℝ) := by norm_num
      _ = Real.pi / 4 := Real.arctan_one
  have h_arctan_seven_lt_angle :
      Real.arctan ((7 : ℝ) / 10) < 35 * Real.pi / 180 := by
    have hangle : 35 * Real.pi / 180 = Real.pi / 4 - Real.pi / 18 := by ring
    rw [hangle]
    linarith
  have h_angle_left : -(Real.pi / 2) < 35 * Real.pi / 180 := by
    nlinarith [Real.pi_pos]
  have h_angle_right : 35 * Real.pi / 180 < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have h_tan_bound : (7 : ℝ) / 10 ≤ Real.tan (35 * Real.pi / 180) := by
    have h_arctan_tan :
        Real.arctan (Real.tan (35 * Real.pi / 180)) = 35 * Real.pi / 180 :=
      Real.arctan_tan h_angle_left h_angle_right
    have h_arctan_lt :
        Real.arctan ((7 : ℝ) / 10) < Real.arctan (Real.tan (35 * Real.pi / 180)) := by
      simpa [h_arctan_tan] using h_arctan_seven_lt_angle
    exact le_of_lt ((Real.arctan_lt_arctan_iff).mp h_arctan_lt)
  have h_numeric_goal : 3 * Real.pi / 180 ≤ 9.8 * ((7 : ℝ) / 10) / (250 * 0.514) := by
    nlinarith [Real.pi_lt_d2]
  have h_scaled :
      9.8 * ((7 : ℝ) / 10) / (250 * 0.514) ≤
        9.8 * Real.tan (35 * Real.pi / 180) / (250 * 0.514) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left h_tan_bound (by norm_num : (0 : ℝ) ≤ 9.8))
      (by norm_num : (0 : ℝ) ≤ 250 * (0.514 : ℝ))
  calc
    3 * Real.pi / 180 ≤ 9.8 * ((7 : ℝ) / 10) / (250 * 0.514) := h_numeric_goal
    _ ≤ 9.8 * Real.tan (35 * Real.pi / 180) / (250 * 0.514) := h_scaled
    _ = tr (35 * Real.pi / 180) := by rw [tr]
