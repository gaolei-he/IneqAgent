import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

noncomputable section

def atanPoly (x : ℝ) : ℝ :=
  x - (11184811 / 33554432) * x ^ 3
    - (13421773 / 67108864) * x ^ 5

def atanErr (x : ℝ) : ℝ :=
  Real.arctan x - atanPoly x

theorem atan_implementation :
    ∀ x : ℝ, |x| ≤ 0.33 →
      |atanErr x| ≤ (2 : ℝ) ^ (-9 : ℤ) := by
  intro x hx
  have hx_interval : -(0.33 : ℝ) ≤ x ∧ x ≤ (0.33 : ℝ) := by
    exact abs_le.mp hx
  have hx_abs_lt_one : |x| < (1 : ℝ) := by
    exact lt_of_le_of_lt hx (by norm_num)
  have hx_sq_le : x ^ 2 ≤ (0.33 : ℝ) ^ 2 := by
    rw [sq_le_sq]
    exact le_trans hx (by norm_num)
  have h_rhs_value : (2 : ℝ) ^ (-9 : ℤ) = (1 / 512 : ℝ) := by
    norm_num
  have h_arctan_series :
      HasSum
        (fun n : ℕ => (-1 : ℝ) ^ n * x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
        (Real.arctan x) := by
    exact Real.hasSum_arctan (by simpa [Real.norm_eq_abs] using hx_abs_lt_one)
  have h_arctan_series_tsum :
      (∑' n : ℕ,
          (-1 : ℝ) ^ n * x ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
        = Real.arctan x := by
    exact h_arctan_series.tsum_eq
  have h_arctan_partial3 :
      (∑ i ∈ Finset.range 3,
          (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ))
        = x - (1 / 3 : ℝ) * x ^ 3 + (1 / 5 : ℝ) * x ^ 5 := by
    norm_num [Finset.sum_range_succ]
    ring
  have h_cubic_delta :
      (11184811 / 33554432 : ℝ) - (1 / 3 : ℝ) = 1 / 100663296 := by
    norm_num
  have h_quintic_delta :
      (13421773 / 67108864 : ℝ) + (1 / 5 : ℝ) = 134217729 / 335544320 := by
    norm_num
  have h_error_decomp :
      atanErr x =
        (Real.arctan x - (x - (1 / 3 : ℝ) * x ^ 3 + (1 / 5 : ℝ) * x ^ 5))
          + (((11184811 / 33554432 : ℝ) - (1 / 3 : ℝ)) * x ^ 3
            + ((13421773 / 67108864 : ℝ) + (1 / 5 : ℝ)) * x ^ 5) := by
    unfold atanErr atanPoly
    ring
  have h_error_decomp_normalized :
      atanErr x =
        (Real.arctan x - (x - (1 / 3 : ℝ) * x ^ 3 + (1 / 5 : ℝ) * x ^ 5))
          + ((1 / 100663296 : ℝ) * x ^ 3
            + (134217729 / 335544320 : ℝ) * x ^ 5) := by
    rw [h_error_decomp, h_cubic_delta, h_quintic_delta]
  have hx_abs_pow_three_le : |x ^ 3| ≤ (0.33 : ℝ) ^ 3 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 3
  have hx_abs_pow_five_le : |x ^ 5| ≤ (0.33 : ℝ) ^ 5 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) hx 5
  have h_coeff_error_abs_le :
      |(1 / 100663296 : ℝ) * x ^ 3
          + (134217729 / 335544320 : ℝ) * x ^ 5|
        ≤ (1 / 100663296 : ℝ) * (0.33 : ℝ) ^ 3
          + (134217729 / 335544320 : ℝ) * (0.33 : ℝ) ^ 5 := by
    calc
      |(1 / 100663296 : ℝ) * x ^ 3
          + (134217729 / 335544320 : ℝ) * x ^ 5|
          ≤ |(1 / 100663296 : ℝ) * x ^ 3|
              + |(134217729 / 335544320 : ℝ) * x ^ 5| := by
            exact abs_add_le _ _
      _ = (1 / 100663296 : ℝ) * |x ^ 3|
              + (134217729 / 335544320 : ℝ) * |x ^ 5| := by
            rw [abs_mul, abs_mul]
            norm_num
      _ ≤ (1 / 100663296 : ℝ) * (0.33 : ℝ) ^ 3
              + (134217729 / 335544320 : ℝ) * (0.33 : ℝ) ^ 5 := by
            gcongr
  have h_coeff_error_abs_small :
      |(1 / 100663296 : ℝ) * x ^ 3
          + (134217729 / 335544320 : ℝ) * x ^ 5|
        ≤ (1 / 600 : ℝ) := by
    exact h_coeff_error_abs_le.trans (by norm_num)
  have h_arctan_remainder_nonneg :
      ∀ y : ℝ, 0 ≤ y → y < 1 →
        |Real.arctan y - (y - (1 / 3 : ℝ) * y ^ 3 + (1 / 5 : ℝ) * y ^ 5)|
          ≤ y ^ 7 / 7 := by
    intro y hy0 hy1
    have h_terms_antitone :
        Antitone (fun n : ℕ => y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
      have hyle : y ≤ 1 := le_of_lt hy1
      refine antitone_nat_of_succ_le fun n => ?_
      change y ^ (2 * n + 3) / (((2 * n + 3 : ℕ) : ℝ)) ≤
        y ^ (2 * n + 1) / (((2 * n + 1 : ℕ) : ℝ))
      have hnum : y ^ (2 * n + 3) ≤ y ^ (2 * n + 1) := by
        apply pow_le_pow_of_le_one hy0 hyle
        omega
      have hden_nat : 2 * n + 1 ≤ 2 * n + 3 := by omega
      have hden :
          (((2 * n + 1 : ℕ) : ℝ)) ≤ (((2 * n + 3 : ℕ) : ℝ)) := by
        exact_mod_cast hden_nat
      calc
        y ^ (2 * n + 3) / (((2 * n + 3 : ℕ) : ℝ))
            ≤ y ^ (2 * n + 1) / (((2 * n + 3 : ℕ) : ℝ)) := by
              exact div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ y ^ (2 * n + 1) / (((2 * n + 1 : ℕ) : ℝ)) := by
              exact div_le_div_of_nonneg_left (pow_nonneg hy0 _) (by positivity) hden
    have h_terms_summable :
        Summable (fun n : ℕ => y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
      have hy2 : y ^ 2 < 1 := by
        exact (sq_lt_one_iff₀ hy0).2 hy1
      have hpow : Summable fun n : ℕ => y ^ (2 * n + 1) := by
        have hsq : Summable fun n : ℕ => (y ^ 2) ^ n :=
          summable_geometric_of_lt_one (by positivity) hy2
        convert hsq.mul_left y using 1
        ext n
        ring
      refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hpow
      intro n
      have hden_one_nat : 1 ≤ 2 * n + 1 := by omega
      have hden_one : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
        exact_mod_cast hden_one_nat
      exact div_le_self (pow_nonneg hy0 _) hden_one
    have h_alt_bound := alternating_series_error_bound
      (fun n : ℕ => y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
      h_terms_antitone h_terms_summable 3
    have h_arctan_series :
        HasSum
          (fun n : ℕ =>
            (-1 : ℝ) ^ n * (y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)))
          (Real.arctan y) := by
      convert Real.hasSum_arctan (x := y)
        (by simpa [Real.norm_eq_abs, abs_of_nonneg hy0] using hy1) using 1
      ext n
      ring
    have h_arctan_tsum :
        (∑' n : ℕ,
            (-1 : ℝ) ^ n * (y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)))
          = Real.arctan y := by
      exact h_arctan_series.tsum_eq
    have h_partial3 :
        (∑ i ∈ Finset.range 3,
            (-1 : ℝ) ^ i * (y ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)))
          = y - (1 / 3 : ℝ) * y ^ 3 + (1 / 5 : ℝ) * y ^ 5 := by
      norm_num [Finset.sum_range_succ]
      ring
    calc
      |Real.arctan y - (y - (1 / 3 : ℝ) * y ^ 3 + (1 / 5 : ℝ) * y ^ 5)|
          = |(∑' n : ℕ,
                (-1 : ℝ) ^ n * (y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)))
              - (∑ i ∈ Finset.range 3,
                  (-1 : ℝ) ^ i * (y ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)))| := by
            rw [h_arctan_tsum, h_partial3]
      _ ≤ y ^ (2 * 3 + 1) / (((2 * 3 + 1 : ℕ) : ℝ)) := h_alt_bound
      _ = y ^ 7 / 7 := by norm_num
  have h_arctan_remainder_abs_le :
      |Real.arctan x - (x - (1 / 3 : ℝ) * x ^ 3 + (1 / 5 : ℝ) * x ^ 5)|
        ≤ |x| ^ 7 / 7 := by
    by_cases hx0 : 0 ≤ x
    · have hpos := h_arctan_remainder_nonneg x hx0
        (by simpa [abs_of_nonneg hx0] using hx_abs_lt_one)
      simpa [abs_of_nonneg hx0] using hpos
    · have hxlt : x < 0 := lt_of_not_ge hx0
      have hneg_nonneg : 0 ≤ -x := by linarith
      have hneg_lt_one : -x < 1 := by
        simpa [abs_of_neg hxlt] using hx_abs_lt_one
      have hpos := h_arctan_remainder_nonneg (-x) hneg_nonneg hneg_lt_one
      have hodd :
          Real.arctan (-x)
              - ((-x) - (1 / 3 : ℝ) * (-x) ^ 3 + (1 / 5 : ℝ) * (-x) ^ 5)
            =
          -(Real.arctan x - (x - (1 / 3 : ℝ) * x ^ 3 + (1 / 5 : ℝ) * x ^ 5)) := by
        rw [Real.arctan_neg]
        ring
      calc
        |Real.arctan x - (x - (1 / 3 : ℝ) * x ^ 3 + (1 / 5 : ℝ) * x ^ 5)|
            = |Real.arctan (-x)
                - ((-x) - (1 / 3 : ℝ) * (-x) ^ 3 + (1 / 5 : ℝ) * (-x) ^ 5)| := by
              rw [hodd, abs_neg]
        _ ≤ (-x) ^ 7 / 7 := hpos
        _ = |x| ^ 7 / 7 := by rw [abs_of_neg hxlt]
  have h_arctan_remainder_abs_small :
      |Real.arctan x - (x - (1 / 3 : ℝ) * x ^ 3 + (1 / 5 : ℝ) * x ^ 5)|
        ≤ (0.33 : ℝ) ^ 7 / 7 := by
    calc
      |Real.arctan x - (x - (1 / 3 : ℝ) * x ^ 3 + (1 / 5 : ℝ) * x ^ 5)|
          ≤ |x| ^ 7 / 7 := h_arctan_remainder_abs_le
      _ ≤ (0.33 : ℝ) ^ 7 / 7 := by
            exact div_le_div_of_nonneg_right
              (pow_le_pow_left₀ (abs_nonneg x) hx 7) (by norm_num)
  rw [h_rhs_value]
  calc
    |atanErr x|
        ≤ |Real.arctan x - (x - (1 / 3 : ℝ) * x ^ 3 + (1 / 5 : ℝ) * x ^ 5)|
            + |(1 / 100663296 : ℝ) * x ^ 3
                + (134217729 / 335544320 : ℝ) * x ^ 5| := by
          rw [h_error_decomp_normalized]
          exact abs_add_le _ _
    _ ≤ (0.33 : ℝ) ^ 7 / 7 + (1 / 600 : ℝ) := by
          exact add_le_add h_arctan_remainder_abs_small h_coeff_error_abs_small
    _ ≤ (1 / 512 : ℝ) := by norm_num
