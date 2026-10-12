import Mathlib

lemma t9b (b : ℝ) : (9 : ℝ) ^ (-b) = (3 : ℝ) ^ (2 * (-b)) := by
  have h9 : (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) := by norm_num
  rw [h9, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (2 : ℝ) (-b)]

lemma t27c (c : ℝ) : (27 : ℝ) ^ (-c) = (3 : ℝ) ^ (3 * (-c)) := by
  have h27 : (27 : ℝ) = (3 : ℝ) ^ (3 : ℝ) := by norm_num
  rw [h27, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (3 : ℝ) (-c)]

lemma amgm3 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    3 * (x * y * z) ^ (1 / 3 : ℝ) ≤ x + y + z := by
  have hgeom : x ^ (1/3 : ℝ) * y ^ (1/3 : ℝ) * z ^ (1/3 : ℝ) ≤
      (1/3 : ℝ) * x + (1/3 : ℝ) * y + (1/3 : ℝ) * z := by
    have hw : (1/3 : ℝ) + (1/3 : ℝ) + (1/3 : ℝ) = 1 := by norm_num
    have h := Real.geom_mean_le_arith_mean3_weighted (w₁ := (1/3:ℝ)) (w₂ := (1/3:ℝ))
      (w₃ := (1/3:ℝ)) (p₁ := x) (p₂ := y) (p₃ := z) (by norm_num) (by norm_num)
      (by norm_num) hx hy hz hw
    nlinarith [h]
  have hprod : (x * y * z) ^ (1/3 : ℝ) = x ^ (1/3 : ℝ) * y ^ (1/3 : ℝ) * z ^ (1/3 : ℝ) := by
    calc
      (x * y * z) ^ (1/3 : ℝ) = (x * (y * z)) ^ (1/3 : ℝ) := by rw [mul_assoc]
      _ = x ^ (1/3 : ℝ) * (y * z) ^ (1/3 : ℝ) := by
        rw [Real.mul_rpow hx (mul_nonneg hy hz)]
      _ = x ^ (1/3 : ℝ) * (y ^ (1/3 : ℝ) * z ^ (1/3 : ℝ)) := by
        rw [Real.mul_rpow hy hz]
      _ = x ^ (1/3 : ℝ) * y ^ (1/3 : ℝ) * z ^ (1/3 : ℝ) := by
        rw [← mul_assoc]
  rw [hprod]
  nlinarith [hgeom]

theorem real_p39 (a b c : ℝ) (h : a^2 + 2 * b^2 + 3 * c^2 = 3 / 2) : (3 : ℝ)^(-a) + (9 : ℝ)^(-b) + (27 : ℝ)^(-c) ≥ 1 := by
  rw [t9b b, t27c c]
  have hpos : (0 : ℝ) < 3 := by norm_num
  have h3nonneg : (0 : ℝ) ≤ 3 := by norm_num
  have hnonneg1 : 0 ≤ (3 : ℝ) ^ (-a) := Real.rpow_nonneg h3nonneg (-a)
  have hnonneg2 : 0 ≤ (3 : ℝ) ^ (2 * (-b)) := Real.rpow_nonneg h3nonneg (2 * (-b))
  have hnonneg3 : 0 ≤ (3 : ℝ) ^ (3 * (-c)) := Real.rpow_nonneg h3nonneg (3 * (-c))
  have hAM : 3 * (((3 : ℝ) ^ (-a) * (3 : ℝ) ^ (2 * (-b)) * (3 : ℝ) ^ (3 * (-c))) ^ (1 / 3 : ℝ))
      ≤ (3 : ℝ) ^ (-a) + (3 : ℝ) ^ (2 * (-b)) + (3 : ℝ) ^ (3 * (-c)) := by
    exact amgm3 ((3 : ℝ) ^ (-a)) ((3 : ℝ) ^ (2 * (-b))) ((3 : ℝ) ^ (3 * (-c)))
      hnonneg1 hnonneg2 hnonneg3
  have hSq : (a + 2 * b + 3 * c) ^ 2 ≤ 6 * (a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2) := by
    have hid : 6 * (a ^ 2 + 2 * b ^ 2 + 3 * c ^ 2) - (a + 2 * b + 3 * c) ^ 2 =
        2 * (a - b) ^ 2 + 3 * (a - c) ^ 2 + 6 * (b - c) ^ 2 := by ring
    nlinarith [hid, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have hS : a + 2 * b + 3 * c ≤ 3 := by
    have habs : |a + 2 * b + 3 * c| ≤ 3 := by
      apply abs_le_of_sq_le_sq
      · nlinarith [h, hSq]
      · norm_num
    exact (abs_le.mp habs).2
  have hE : (-1 : ℝ) ≤ (-(a + 2 * b + 3 * c)) / 3 := by
    linarith
  have hbase : (1/3 : ℝ) ≤ (3 : ℝ) ^ (-(a + 2 * b + 3 * c) / 3) := by
    calc
      (1/3 : ℝ) = (3 : ℝ) ^ (-1 : ℝ) := by norm_num
      _ ≤ (3 : ℝ) ^ (-(a + 2 * b + 3 * c) / 3) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hE
  have hprod_eq : (((3 : ℝ) ^ (-a) * (3 : ℝ) ^ (2 * (-b)) * (3 : ℝ) ^ (3 * (-c))) ^ (1 / 3 : ℝ))
      = (3 : ℝ) ^ (-(a + 2 * b + 3 * c) / 3) := by
    have hA : (-a) + 2 * (-b) + 3 * (-c) = -(a + 2 * b + 3 * c) := by ring
    calc
      (((3 : ℝ) ^ (-a) * (3 : ℝ) ^ (2 * (-b)) * (3 : ℝ) ^ (3 * (-c))) ^ (1 / 3 : ℝ))
          = ((3 : ℝ) ^ ((-a) + 2 * (-b)) * (3 : ℝ) ^ (3 * (-c))) ^ (1 / 3 : ℝ) := by
            rw [Real.rpow_add hpos (-a) (2 * (-b))]
      _ = ((3 : ℝ) ^ ((-a) + 2 * (-b) + 3 * (-c))) ^ (1 / 3 : ℝ) := by
            rw [Real.rpow_add hpos ((-a) + 2 * (-b)) (3 * (-c))]
      _ = (3 : ℝ) ^ (((-a) + 2 * (-b) + 3 * (-c)) * (1 / 3 : ℝ)) := by
            rw [← Real.rpow_mul (le_of_lt hpos) ((-a) + 2 * (-b) + 3 * (-c)) (1 / 3 : ℝ)]
      _ = (3 : ℝ) ^ (-(a + 2 * b + 3 * c) / 3) := by
            rw [hA]
            ring_nf
  have hprodlo : (1/3 : ℝ) ≤ (((3 : ℝ) ^ (-a) * (3 : ℝ) ^ (2 * (-b)) * (3 : ℝ) ^ (3 * (-c))) ^ (1 / 3 : ℝ)) := by
    rw [hprod_eq]
    exact hbase
  nlinarith [hAM, hprodlo]
