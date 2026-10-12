import Mathlib

local macro_rules
  | `($x:term ^ (1 / 7)) => `($x ^ (1 / 7 : ℝ))

theorem P42 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a + b + c = a ^ (1 / 7) + b ^ (1 / 7) + c ^ (1 / 7)) : 1 ≤ a ^ a * b ^ b * c ^ c := by
  have pointwise (x : ℝ) (hx : 0 < x) :
      (7 / 6 : ℝ) * (x - x ^ (1 / 7)) ≤ x * Real.log x := by
    have hbase : 1 - (x ^ ((6 : ℝ) / 7))⁻¹ ≤ Real.log (x ^ ((6 : ℝ) / 7)) := by
      exact Real.one_sub_inv_le_log_of_pos (Real.rpow_pos_of_pos hx ((6 : ℝ) / 7))
    have hbase' : 1 - (x ^ ((6 : ℝ) / 7))⁻¹ ≤ ((6 : ℝ) / 7) * Real.log x := by
      simpa [Real.log_rpow hx] using hbase
    have hscaled := mul_le_mul_of_nonneg_left hbase' (by positivity : 0 ≤ (7 / 6 : ℝ) * x)
    have hleft : (7 / 6 : ℝ) * x * (1 - (x ^ ((6 : ℝ) / 7))⁻¹) =
        (7 / 6 : ℝ) * (x - x ^ (1 / 7)) := by
      have hpow_split : x ^ ((6 : ℝ) / 7) * x ^ (1 / 7) = x := by
        calc
          x ^ ((6 : ℝ) / 7) * x ^ (1 / 7) = x ^ (((6 : ℝ) / 7) + (1 / 7 : ℝ)) := by
            rw [← Real.rpow_add hx]
          _ = x := by norm_num
      have hmul_inv : x * (x ^ ((6 : ℝ) / 7))⁻¹ = x ^ (1 / 7) := by
        have hxpow_ne : x ^ ((6 : ℝ) / 7) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx ((6 : ℝ) / 7))
        calc
          x * (x ^ ((6 : ℝ) / 7))⁻¹ = (x ^ ((6 : ℝ) / 7) * x ^ (1 / 7)) * (x ^ ((6 : ℝ) / 7))⁻¹ := by rw [hpow_split]
          _ = x ^ (1 / 7) := by field_simp [hxpow_ne]
      calc
        (7 / 6 : ℝ) * x * (1 - (x ^ ((6 : ℝ) / 7))⁻¹)
            = (7 / 6 : ℝ) * (x - x * (x ^ ((6 : ℝ) / 7))⁻¹) := by ring
        _ = (7 / 6 : ℝ) * (x - x ^ (1 / 7)) := by rw [hmul_inv]
    have hright : (7 / 6 : ℝ) * x * (((6 : ℝ) / 7) * Real.log x) = x * Real.log x := by ring
    calc
      (7 / 6 : ℝ) * (x - x ^ (1 / 7))
          = (7 / 6 : ℝ) * x * (1 - (x ^ ((6 : ℝ) / 7))⁻¹) := hleft.symm
      _ ≤ (7 / 6 : ℝ) * x * (((6 : ℝ) / 7) * Real.log x) := hscaled
      _ = x * Real.log x := hright
  have ha_log_bound := pointwise a ha
  have hb_log_bound := pointwise b hb
  have hc_log_bound := pointwise c hc
  have hlog_sum_nonneg : 0 ≤ a * Real.log a + b * Real.log b + c * Real.log c := by
    have hsum_zero : (7 / 6 : ℝ) * (a - a ^ (1 / 7)) +
          (7 / 6 : ℝ) * (b - b ^ (1 / 7)) +
          (7 / 6 : ℝ) * (c - c ^ (1 / 7)) = 0 := by
      calc
        (7 / 6 : ℝ) * (a - a ^ (1 / 7)) +
            (7 / 6 : ℝ) * (b - b ^ (1 / 7)) +
            (7 / 6 : ℝ) * (c - c ^ (1 / 7))
            = (7 / 6 : ℝ) * ((a + b + c) -
                (a ^ (1 / 7) + b ^ (1 / 7) + c ^ (1 / 7))) := by ring_nf
        _ = 0 := by nlinarith [h]
    nlinarith [ha_log_bound, hb_log_bound, hc_log_bound, hsum_zero]
  have hprod_exp : a ^ a * b ^ b * c ^ c =
      Real.exp (a * Real.log a + b * Real.log b + c * Real.log c) := by
    rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hc]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hprod_exp]
  exact Real.one_le_exp_iff.mpr hlog_sum_nonneg
