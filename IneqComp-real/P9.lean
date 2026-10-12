import Mathlib

open scoped BigOperators

private lemma p9_amgm3pos {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x * y * z = 1) : 3 ≤ x + y + z := by
  have hamgm :=
    @Real.geom_mean_le_arith_mean3_weighted (1 / 3 : ℝ) (1 / 3 : ℝ) (1 / 3 : ℝ) x y z
      (by norm_num) (by norm_num) (by norm_num) hx hy hz (by norm_num)
  have hprod : x ^ (3 : ℝ)⁻¹ * y ^ (3 : ℝ)⁻¹ * z ^ (3 : ℝ)⁻¹ = 1 := by
    rw [← Real.mul_rpow hx hy, ← Real.mul_rpow (mul_nonneg hx hy) hz, h]
    exact Real.one_rpow (3 : ℝ)⁻¹
  have hle : 1 ≤ (1 / 3 : ℝ) * x + (1 / 3 : ℝ) * y + (1 / 3 : ℝ) * z := by
    simpa [hprod] using hamgm
  nlinarith

private lemma p9_titu3 (a b c A B C : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    ((a + b + c)^2) / (a * A + b * B + c * C) ≤ a / A + b / B + c / C := by
  let f : Fin 3 → ℝ := ![a, b, c]
  let g : Fin 3 → ℝ := ![a * A, b * B, c * C]
  have hg : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 < g i := by
    intro i hi
    fin_cases i <;> simp [g] <;> positivity
  have h := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset (Fin 3)) f hg
  have hleft : (∑ i : Fin 3, f i)^2 / (∑ i : Fin 3, g i) =
      ((a + b + c)^2) / (a * A + b * B + c * C) := by
    simp [f, g, Fin.sum_univ_three]
  have hright : (∑ i : Fin 3, (f i)^2 / g i) = a / A + b / B + c / C := by
    simp [f, g, Fin.sum_univ_three]
    field_simp [ha.ne', hb.ne', hc.ne', mul_ne_zero ha.ne' hA.ne', mul_ne_zero hb.ne' hB.ne',
      mul_ne_zero hc.ne' hC.ne']
  rwa [hleft, hright] at h

private lemma p9_ratio_bound (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (huvw : u * v * w = 1) :
    u / (1 + v) + v / (1 + w) + w / (1 + u) ≥ 3 / 2 := by
  let X : ℝ := u + v + w
  let Y : ℝ := u * v + v * w + w * u
  have hX3 : 3 ≤ X := by
    dsimp [X]
    exact p9_amgm3pos hu.le hv.le hw.le huvw
  have hXY : (3 / 2 : ℝ) * (X + Y) ≤ X ^ 2 := by
    dsimp [X, Y]
    have hsq : 0 ≤ (u + v + w) ^ 2 - 3 * (u * v + v * w + w * u) := by
      have hfac : (u + v + w) ^ 2 - 3 * (u * v + v * w + w * u) =
          (1 / 2 : ℝ) * ((u - v) ^ 2 + (v - w) ^ 2 + (w - u) ^ 2) := by
        ring
      rw [hfac]
      positivity
    have hlin : 0 ≤ (u + v + w) * ((u + v + w) - 3) := by
      nlinarith [hX3, sq_nonneg (u + v + w)]
    nlinarith
  have hpos : 0 < u * (1 + v) + v * (1 + w) + w * (1 + u) := by positivity
  have hcauchy := p9_titu3 u v w (1 + v) (1 + w) (1 + u) hu hv hw
    (by positivity) (by positivity) (by positivity)
  have hden : u * (1 + v) + v * (1 + w) + w * (1 + u) = X + Y := by
    dsimp [X, Y]
    ring
  have hposXY : 0 < X + Y := by
    rw [← hden]
    exact hpos
  have hlb : 3 / 2 ≤ (u + v + w) ^ 2 / (u * (1 + v) + v * (1 + w) + w * (1 + u)) := by
    rw [hden]
    dsimp [X, Y] at hXY
    rw [le_div_iff₀ hposXY]
    exact hXY
  exact le_trans hlb hcauchy

set_option maxHeartbeats 4000000 in
theorem real_p9 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = 1) :
    (1 + a) / (1 - a) + (1 + b) / (1 - b) + (1 + c) / (1 - c) ≤ 2 * (a / b + b / c + c / a) := by
  have hbc : b + c ≠ 0 := by positivity
  have hca : c + a ≠ 0 := by positivity
  have hab : a + b ≠ 0 := by positivity
  have hS : a * c / (b * (b + c)) + a * b / (c * (c + a)) + b * c / (a * (a + b)) ≥ 3 / 2 := by
    have hprod : (a / b) * (b / c) * (c / a) = 1 := by
      field_simp [ha.ne', hb.ne', hc.ne']
    have hbnd := p9_ratio_bound (a / b) (b / c) (c / a) (by positivity) (by positivity)
      (by positivity) hprod
    have hterm1 : (a / b) / (1 + b / c) = a * c / (b * (b + c)) := by
      field_simp [hb.ne', hbc]
      ring
    have hterm2 : (b / c) / (1 + c / a) = a * b / (c * (c + a)) := by
      field_simp [hc.ne', hca]
      ring
    have hterm3 : (c / a) / (1 + a / b) = b * c / (a * (a + b)) := by
      field_simp [ha.ne', hab]
      ring
    calc
      3 / 2 ≤ (a / b) / (1 + b / c) + (b / c) / (1 + c / a) + (c / a) / (1 + a / b) := hbnd
      _ = a * c / (b * (b + c)) + a * b / (c * (c + a)) + b * c / (a * (a + b)) := by
            rw [hterm1, hterm2, hterm3]
  rw [show 1 - a = b + c by nlinarith [h],
      show 1 - b = c + a by nlinarith [h],
      show 1 - c = a + b by nlinarith [h]]
  have hL1 : (1 + a) / (b + c) = 1 + 2 * (a / (b + c)) := by
    field_simp [hbc]
    nlinarith [h]
  have hL2 : (1 + b) / (c + a) = 1 + 2 * (b / (c + a)) := by
    field_simp [hca]
    nlinarith [h]
  have hL3 : (1 + c) / (a + b) = 1 + 2 * (c / (a + b)) := by
    field_simp [hab]
    nlinarith [h]
  rw [hL1, hL2, hL3]
  have hT1 : a / b - a / (b + c) = a * c / (b * (b + c)) := by
    field_simp [hb.ne', hbc]
    ring
  have hT2 : b / c - b / (c + a) = a * b / (c * (c + a)) := by
    field_simp [hc.ne', hca]
    ring
  have hT3 : c / a - c / (a + b) = b * c / (a * (a + b)) := by
    field_simp [ha.ne', hab]
    ring
  have hdiff : (a / b + b / c + c / a) - (a / (b + c) + b / (c + a) + c / (a + b)) =
      (a / b - a / (b + c)) + (b / c - b / (c + a)) + (c / a - c / (a + b)) := by
    nlinarith
  have hle_sum : (a / b + b / c + c / a) - (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2 := by
    nlinarith [hS, hT1, hT2, hT3, hdiff]
  nlinarith
