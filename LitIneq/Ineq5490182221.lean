import Mathlib

set_option linter.style.header false
set_option maxHeartbeats 800000

noncomputable section

def atn2 (x y : ℝ) : ℝ :=
  Real.arctan (y / x)

def deltaX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  x1 * x4 * (-x1 + x2 + x3 - x4 + x5 + x6)
  + x2 * x5 * (x1 - x2 + x3 + x4 - x5 + x6)
  + x3 * x6 * (x1 + x2 - x3 + x4 + x5 - x6)
  - x2 * x3 * x4 - x1 * x3 * x5 - x1 * x2 * x6 - x4 * x5 * x6

def deltaX4 (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  -x2 * x3 - x1 * x4 + x2 * x5 + x3 * x6 - x5 * x6
  + x1 * (-x1 + x2 + x3 - x4 + x5 + x6)

def dihX (x1 x2 x3 x4 x5 x6 : ℝ) : ℝ :=
  let dX4 := deltaX4 x1 x2 x3 x4 x5 x6
  let d := deltaX x1 x2 x3 x4 x5 x6
  Real.pi / 2 + atn2 (Real.sqrt (4 * x1 * d)) (-dX4)

-- Helper lemmas used to reduce the transcendental dihedral bound to a purely
-- algebraic nonnegativity condition on bounded offset variables.

lemma offset_pair_bracket_nonneg {u v : ℝ}
    (hu : u ≤ 2.3504) (hv0 : 0 ≤ v) (hv : v ≤ 2.3504) :
    0 ≤ 16 - 4 * u - u * v := by
  have huv : u * v ≤ 2.3504 * 2.3504 := by
    exact mul_le_mul hu hv hv0 (by norm_num)
  nlinarith

lemma offset_gap_nonneg {u : ℝ} (hu : u ≤ 2.3504) :
    0 ≤ 4 - u := by
  norm_num at hu ⊢
  linarith

lemma offset_deltaX4_core_le_twenty {u v : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 2.3504)
    (hv0 : 0 ≤ v) (hv : v ≤ 2.3504) :
    u ^ 2 + 2 * u * v + 8 * v - 16 ≤ 20 := by
  have hu_sq : u ^ 2 ≤ 2.3504 ^ 2 := by
    have hmul : u * u ≤ 2.3504 * 2.3504 := by
      exact mul_le_mul hu hu hu0 (by norm_num)
    simpa [pow_two] using hmul
  have huv : u * v ≤ 2.3504 * 2.3504 := by
    exact mul_le_mul hu hv hv0 (by norm_num)
  have hlin : 8 * v ≤ 8 * 2.3504 := by
    exact mul_le_mul_of_nonneg_left hv (by norm_num)
  nlinarith

lemma arctan_one_third_lt_322_div_1000 :
    Real.arctan ((1 : ℝ) / 3) < (322 : ℝ) / 1000 := by
  have hy0 : (0 : ℝ) ≤ (1 : ℝ) / 3 := by norm_num
  have h_terms_antitone :
      Antitone
        (fun n : ℕ =>
          ((1 : ℝ) / 3) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
    have hyle : ((1 : ℝ) / 3) ≤ 1 := by norm_num
    refine antitone_nat_of_succ_le fun n => ?_
    change ((1 : ℝ) / 3) ^ (2 * n + 3) / (((2 * n + 3 : ℕ) : ℝ)) ≤
      ((1 : ℝ) / 3) ^ (2 * n + 1) / (((2 * n + 1 : ℕ) : ℝ))
    have hnum :
        ((1 : ℝ) / 3) ^ (2 * n + 3) ≤
          ((1 : ℝ) / 3) ^ (2 * n + 1) := by
      apply pow_le_pow_of_le_one hy0 hyle
      omega
    have hden_nat : 2 * n + 1 ≤ 2 * n + 3 := by omega
    have hden :
        (((2 * n + 1 : ℕ) : ℝ)) ≤ (((2 * n + 3 : ℕ) : ℝ)) := by
      exact_mod_cast hden_nat
    calc
      ((1 : ℝ) / 3) ^ (2 * n + 3) / (((2 * n + 3 : ℕ) : ℝ))
          ≤ ((1 : ℝ) / 3) ^ (2 * n + 1) /
              (((2 * n + 3 : ℕ) : ℝ)) := by
            exact div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ ((1 : ℝ) / 3) ^ (2 * n + 1) /
              (((2 * n + 1 : ℕ) : ℝ)) := by
            exact div_le_div_of_nonneg_left (pow_nonneg hy0 _) (by positivity) hden
  have h_terms_summable :
      Summable
        (fun n : ℕ =>
          ((1 : ℝ) / 3) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
    have hy2 : ((1 : ℝ) / 3) ^ 2 < 1 := by norm_num
    have hpow : Summable fun n : ℕ => ((1 : ℝ) / 3) ^ (2 * n + 1) := by
      have hsq : Summable fun n : ℕ => (((1 : ℝ) / 3) ^ 2) ^ n :=
        summable_geometric_of_lt_one (by positivity) hy2
      convert hsq.mul_left ((1 : ℝ) / 3) using 1
      ext n
      rw [← pow_mul]
      rw [show 2 * n + 1 = 1 + 2 * n by omega]
      rw [pow_add]
      ring
    refine Summable.of_nonneg_of_le (fun n => by positivity) ?_ hpow
    intro n
    have hden_one_nat : 1 ≤ 2 * n + 1 := by omega
    have hden_one : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast hden_one_nat
    exact div_le_self (pow_nonneg hy0 _) hden_one
  have h_alt_bound := alternating_series_error_bound
    (fun n : ℕ =>
      ((1 : ℝ) / 3) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
    h_terms_antitone h_terms_summable 3
  have h_arctan_series :
      HasSum
        (fun n : ℕ =>
          (-1 : ℝ) ^ n *
            (((1 : ℝ) / 3) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)))
        (Real.arctan ((1 : ℝ) / 3)) := by
    convert Real.hasSum_arctan (x := ((1 : ℝ) / 3))
      (by norm_num [Real.norm_eq_abs]) using 1
    · ext n
      ring
  have h_arctan_tsum :
      (∑' n : ℕ,
          (-1 : ℝ) ^ n *
            (((1 : ℝ) / 3) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)))
        = Real.arctan ((1 : ℝ) / 3) := by
    exact h_arctan_series.tsum_eq
  have h_partial3 :
      (∑ i ∈ Finset.range 3,
          (-1 : ℝ) ^ i *
            (((1 : ℝ) / 3) ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)))
        = ((1 : ℝ) / 3) - (1 / 3 : ℝ) * ((1 : ℝ) / 3) ^ 3
            + (1 / 5 : ℝ) * ((1 : ℝ) / 3) ^ 5 := by
    norm_num [Finset.sum_range_succ]
  have h_abs :
      |Real.arctan ((1 : ℝ) / 3)
          - (((1 : ℝ) / 3) - (1 / 3 : ℝ) * ((1 : ℝ) / 3) ^ 3
            + (1 / 5 : ℝ) * ((1 : ℝ) / 3) ^ 5)|
        ≤ ((1 : ℝ) / 3) ^ 7 / 7 := by
    calc
      |Real.arctan ((1 : ℝ) / 3)
          - (((1 : ℝ) / 3) - (1 / 3 : ℝ) * ((1 : ℝ) / 3) ^ 3
            + (1 / 5 : ℝ) * ((1 : ℝ) / 3) ^ 5)|
          = |(∑' n : ℕ,
                (-1 : ℝ) ^ n *
                  (((1 : ℝ) / 3) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)))
              - (∑ i ∈ Finset.range 3,
                  (-1 : ℝ) ^ i *
                    (((1 : ℝ) / 3) ^ (2 * i + 1) /
                      ((2 * i + 1 : ℕ) : ℝ)))| := by
            rw [h_arctan_tsum, h_partial3]
      _ ≤ ((1 : ℝ) / 3) ^ (2 * 3 + 1) / (((2 * 3 + 1 : ℕ) : ℝ)) :=
        h_alt_bound
      _ = ((1 : ℝ) / 3) ^ 7 / 7 := by norm_num
  have h_upper :
      Real.arctan ((1 : ℝ) / 3)
        ≤ (((1 : ℝ) / 3) - (1 / 3 : ℝ) * ((1 : ℝ) / 3) ^ 3
            + (1 / 5 : ℝ) * ((1 : ℝ) / 3) ^ 5)
          + ((1 : ℝ) / 3) ^ 7 / 7 := by
    have hle_abs :
        Real.arctan ((1 : ℝ) / 3)
          - (((1 : ℝ) / 3) - (1 / 3 : ℝ) * ((1 : ℝ) / 3) ^ 3
            + (1 / 5 : ℝ) * ((1 : ℝ) / 3) ^ 5)
          ≤ |Real.arctan ((1 : ℝ) / 3)
              - (((1 : ℝ) / 3) - (1 / 3 : ℝ) * ((1 : ℝ) / 3) ^ 3
                + (1 / 5 : ℝ) * ((1 : ℝ) / 3) ^ 5)| := le_abs_self _
    linarith
  nlinarith

lemma pi_half_add_arctan_one_third_lt_1893 :
    Real.pi / 2 + Real.arctan ((1 : ℝ) / 3) < 1.893 := by
  have hpi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have hatan : Real.arctan ((1 : ℝ) / 3) < (322 : ℝ) / 1000 :=
    arctan_one_third_lt_322_div_1000
  nlinarith

lemma ratio_le_one_third_of_sq_le_nonneg_case {A N : ℝ}
    (hApos : 0 < A) (hsqrt_pos : 0 < Real.sqrt A)
    (hquad : 0 ≤ N → 9 * N ^ 2 ≤ A) :
    N / Real.sqrt A ≤ 1 / 3 := by
  by_cases hN : N ≤ 0
  · rw [div_le_iff₀ hsqrt_pos]
    have hright_nonneg : 0 ≤ ((1 : ℝ) / 3) * Real.sqrt A := by positivity
    nlinarith
  · have hNpos : 0 < N := lt_of_not_ge hN
    rw [div_le_iff₀ hsqrt_pos]
    have h3N_nonneg : 0 ≤ 3 * N := by nlinarith
    have hsqrt_nonneg : 0 ≤ Real.sqrt A := le_of_lt hsqrt_pos
    have hsq : (3 * N) ^ 2 ≤ (Real.sqrt A) ^ 2 := by
      calc
        (3 * N) ^ 2 = 9 * N ^ 2 := by ring
        _ ≤ A := hquad (le_of_lt hNpos)
        _ = (Real.sqrt A) ^ 2 := by
          rw [Real.sq_sqrt (le_of_lt hApos)]
    have hle_abs : |3 * N| ≤ |Real.sqrt A| := sq_le_sq.mp hsq
    rw [abs_of_nonneg h3N_nonneg, abs_of_nonneg hsqrt_nonneg] at hle_abs
    nlinarith

-- When the six offsets satisfy the box bounds and the shifted numerator is
-- nonnegative, the numerator's cross terms cannot exceed the pair term.
lemma offset_tail_term_nonpos {a1 a2 a3 a5 a6 : ℝ}
    (ha1n : 0 ≤ a1) (ha2n : 0 ≤ a2)
    (ha3n : 0 ≤ a3) (ha3h : a3 ≤ 2.3504)
    (ha5n : 0 ≤ a5)
    (ha6n : 0 ≤ a6) (ha6h : a6 ≤ 2.3504) :
    a2 * a3 - a1 * a2 - a1 * a3 - a2 * a5 - 4 * a2
      - a3 * a6 - 4 * a3 - a1 * a5 - a1 * a6
      + a5 * a6 - 4 * a5 - 4 * a6 ≤ 0 := by
  let S : ℝ := a2 + a3 + a5 + a6
  have hA :
      a2 * a3 + a5 * a6 - (a1 + 4) * S ≤ 0 := by
    have ha3_le4 : a3 ≤ (4 : ℝ) := by linarith
    have ha6_le4 : a6 ≤ (4 : ℝ) := by linarith
    have h23 : a2 * a3 ≤ 4 * a2 := by
      have hmul : a2 * a3 ≤ a2 * 4 :=
        mul_le_mul_of_nonneg_left ha3_le4 ha2n
      simpa [mul_comm] using hmul
    have h56 : a5 * a6 ≤ 4 * a5 := by
      have hmul : a5 * a6 ≤ a5 * 4 :=
        mul_le_mul_of_nonneg_left ha6_le4 ha5n
      simpa [mul_comm] using hmul
    have hS0 : 0 ≤ S := by
      dsimp [S]
      nlinarith
    have ha1S : 0 ≤ a1 * S := mul_nonneg ha1n hS0
    dsimp [S]
    nlinarith
  have htail :
      a2 * a3 - a1 * a2 - a1 * a3 - a2 * a5 - 4 * a2
        - a3 * a6 - 4 * a3 - a1 * a5 - a1 * a6
        + a5 * a6 - 4 * a5 - 4 * a6
      = a2 * a3 + a5 * a6 - (a1 + 4) * S - a2 * a5 - a3 * a6 := by
    dsimp [S]
    ring
  have ha2a5 : 0 ≤ a2 * a5 := mul_nonneg ha2n ha5n
  have ha3a6 : 0 ≤ a3 * a6 := mul_nonneg ha3n ha6n
  rw [htail]
  nlinarith

-- Two-variable algebraic certificate for the remaining polynomial condition.
-- With u, v in the offset box and (u+4)(u+2v-4) = pair term nonnegative, one has
--   4*(u+4)*D - 9*B^2 ≥ 0
-- for the pair lower bound D of the shifted delta and B the pair numerator.
lemma pair_shift_quad_nonneg {u v : ℝ}
    (hu0 : 0 ≤ u) (hu : u ≤ 2.3504)
    (hv : v ≤ 2.3504)
    (hbase : 0 ≤ u ^ 2 + 2 * u * v + 8 * v - 16) :
    0 ≤ 4 * (u + 4)
          * (128 + 16 * u - 4 * u ^ 2 - u ^ 2 * v
              + 16 * v - 4 * v ^ 2 - u * v ^ 2)
      - 9 * (u ^ 2 + 2 * u * v + 8 * v - 16) ^ 2 := by
  have hlin : 0 ≤ u + 2 * v - 4 := by
    have hfac :
        u ^ 2 + 2 * u * v + 8 * v - 16
          = (u + 4) * (u + 2 * v - 4) := by
      ring
    have hu4_pos : 0 < u + 4 := by nlinarith [hu0]
    nlinarith
  let R : ℝ := 9 * u ^ 2 + 40 * u * v + 40 * v ^ 2
    - 56 * u - 160 * v + 16
  have hRle : R ≤ 0 := by
    have hR_expr : R = 10 * (u + 2 * v - 4) ^ 2 - (u - 12) ^ 2 := by
      dsimp [R]
      ring
    rw [hR_expr]
    have hs0 : 0 ≤ u + 2 * v - 4 := hlin
    have hs_ub : u + 2 * v - 4 ≤ 3 * (2.3504 : ℝ) - 4 := by
      nlinarith [hu, hv]
    have hK_nonneg : 0 ≤ 3 * (2.3504 : ℝ) - 4 := by norm_num
    have hsq_ub :
        (u + 2 * v - 4) ^ 2 ≤ (3 * (2.3504 : ℝ) - 4) ^ 2 := by
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg hs0, abs_of_nonneg hK_nonneg]
        exact hs_ub)
    have hu12_nonneg : 0 ≤ 12 - u := by nlinarith [hu]
    have hu12_ge : 12 - (2.3504 : ℝ) ≤ 12 - u := by
      nlinarith [hu]
    have hL_nonneg : 0 ≤ 12 - (2.3504 : ℝ) := by norm_num
    have h_u12_sq :
        (12 - (2.3504 : ℝ)) ^ 2 ≤ (u - 12) ^ 2 := by
      rw [show (u - 12) ^ 2 = (12 - u) ^ 2 by ring]
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg hu12_nonneg, abs_of_nonneg hL_nonneg]
        exact hu12_ge)
    have hnum :
        10 * (3 * (2.3504 : ℝ) - 4) ^ 2
          ≤ (12 - (2.3504 : ℝ)) ^ 2 := by
      norm_num
    nlinarith
  have hQ_expr :
      4 * (u + 4)
          * (128 + 16 * u - 4 * u ^ 2 - u ^ 2 * v
              + 16 * v - 4 * v ^ 2 - u * v ^ 2)
        - 9 * (u ^ 2 + 2 * u * v + 8 * v - 16) ^ 2
      = -(u + 4) ^ 2 * R := by
    dsimp [R]
    ring
  have hnonneg : 0 ≤ (u + 4) ^ 2 * (-R) :=
    mul_nonneg (sq_nonneg (u + 4)) (neg_nonneg.mpr hRle)
  rw [hQ_expr]
  have hrewrite : -(u + 4) ^ 2 * R = (u + 4) ^ 2 * (-R) := by ring
  rwa [hrewrite]

theorem ineq5490182221 :
    ∀ x1 x2 x3 x4 x5 x6 : ℝ,
      4.0 ≤ x1 ∧ x1 ≤ 6.3504 ∧
      4.0 ≤ x2 ∧ x2 ≤ 6.3504 ∧
      4.0 ≤ x3 ∧ x3 ≤ 6.3504 ∧
      4.0 ≤ x4 ∧ x4 ≤ 6.3504 ∧
      4.0 ≤ x5 ∧ x5 ≤ 6.3504 ∧
      4.0 ≤ x6 ∧ x6 ≤ 6.3504 →
        dihX x1 x2 x3 x4 x5 x6
        + (-1.893) < 0 := by
  intro x1 x2 x3 x4 x5 x6 hbox
  rcases hbox with
    ⟨hx1_lo, hx1_hi, hx2_lo, hx2_hi, hx3_lo, hx3_hi,
      hx4_lo, hx4_hi, hx5_lo, hx5_hi, hx6_lo, hx6_hi⟩
  have hx1_pos : 0 < x1 := by linarith
  have hx2_pos : 0 < x2 := by linarith
  have hx3_pos : 0 < x3 := by linarith
  have hx4_pos : 0 < x4 := by linarith
  have hx5_pos : 0 < x5 := by linarith
  have hx6_pos : 0 < x6 := by linarith
  have hx1_nonneg : 0 ≤ x1 := le_of_lt hx1_pos
  have hx2_nonneg : 0 ≤ x2 := le_of_lt hx2_pos
  have hx3_nonneg : 0 ≤ x3 := le_of_lt hx3_pos
  have hx4_nonneg : 0 ≤ x4 := le_of_lt hx4_pos
  have hx5_nonneg : 0 ≤ x5 := le_of_lt hx5_pos
  have hx6_nonneg : 0 ≤ x6 := le_of_lt hx6_pos
  let a1 : ℝ := x1 - 4
  let a2 : ℝ := x2 - 4
  let a3 : ℝ := x3 - 4
  let a4 : ℝ := x4 - 4
  let a5 : ℝ := x5 - 4
  let a6 : ℝ := x6 - 4
  have hx1_offset : x1 = a1 + 4 := by
    dsimp [a1]
    linarith
  have hx2_offset : x2 = a2 + 4 := by
    dsimp [a2]
    linarith
  have hx3_offset : x3 = a3 + 4 := by
    dsimp [a3]
    linarith
  have hx4_offset : x4 = a4 + 4 := by
    dsimp [a4]
    linarith
  have hx5_offset : x5 = a5 + 4 := by
    dsimp [a5]
    linarith
  have hx6_offset : x6 = a6 + 4 := by
    dsimp [a6]
    linarith
  have ha1_nonneg : 0 ≤ a1 := by
    dsimp [a1]
    linarith
  have ha2_nonneg : 0 ≤ a2 := by
    dsimp [a2]
    linarith
  have ha3_nonneg : 0 ≤ a3 := by
    dsimp [a3]
    linarith
  have ha4_nonneg : 0 ≤ a4 := by
    dsimp [a4]
    linarith
  have ha5_nonneg : 0 ≤ a5 := by
    dsimp [a5]
    linarith
  have ha6_nonneg : 0 ≤ a6 := by
    dsimp [a6]
    linarith
  have ha1_hi : a1 ≤ 2.3504 := by
    dsimp [a1]
    linarith
  have ha2_hi : a2 ≤ 2.3504 := by
    dsimp [a2]
    linarith
  have ha3_hi : a3 ≤ 2.3504 := by
    dsimp [a3]
    linarith
  have ha4_hi : a4 ≤ 2.3504 := by
    dsimp [a4]
    linarith
  have ha5_hi : a5 ≤ 2.3504 := by
    dsimp [a5]
    linarith
  have ha6_hi : a6 ≤ 2.3504 := by
    dsimp [a6]
    linarith
  have hb14 : 0 ≤ 16 - 4 * a1 - a1 * a4 :=
    offset_pair_bracket_nonneg ha1_hi ha4_nonneg ha4_hi
  have hb41 : 0 ≤ 16 - 4 * a4 - a1 * a4 := by
    simpa [mul_comm] using offset_pair_bracket_nonneg ha4_hi ha1_nonneg ha1_hi
  have hb25 : 0 ≤ 16 - 4 * a2 - a2 * a5 :=
    offset_pair_bracket_nonneg ha2_hi ha5_nonneg ha5_hi
  have hb52 : 0 ≤ 16 - 4 * a5 - a2 * a5 := by
    simpa [mul_comm] using offset_pair_bracket_nonneg ha5_hi ha2_nonneg ha2_hi
  have hb36 : 0 ≤ 16 - 4 * a3 - a3 * a6 :=
    offset_pair_bracket_nonneg ha3_hi ha6_nonneg ha6_hi
  have hb63 : 0 ≤ 16 - 4 * a6 - a3 * a6 := by
    simpa [mul_comm] using offset_pair_bracket_nonneg ha6_hi ha3_nonneg ha3_hi
  have h4a3 : 0 ≤ 4 - a3 := offset_gap_nonneg ha3_hi
  have h4a5 : 0 ≤ 4 - a5 := offset_gap_nonneg ha5_hi
  have h4a6 : 0 ≤ 4 - a6 := offset_gap_nonneg ha6_hi
  have hdelta_split :
      deltaX x1 x2 x3 x4 x5 x6 =
        128
          + a1 * (16 - 4 * a1 - a1 * a4)
          + a4 * (16 - 4 * a4 - a1 * a4)
          + a2 * (16 - 4 * a2 - a2 * a5)
          + a5 * (16 - 4 * a5 - a2 * a5)
          + a3 * (16 - 4 * a3 - a3 * a6)
          + a6 * (16 - 4 * a6 - a3 * a6)
          + a1 * a2 * (4 - a6)
          + a1 * a3 * (4 - a5)
          + a4 * a2 * (4 - a3)
          + a4 * a5 * (4 - a6)
          + a1 * a2 * a4 + a1 * a2 * a5
          + a1 * a3 * a4 + a1 * a3 * a6
          + a1 * a4 * a5 + a1 * a4 * a6
          + 4 * a1 * a5 + 4 * a1 * a6
          + a2 * a3 * a5 + a2 * a3 * a6
          + 4 * a2 * a3 + a2 * a4 * a5
          + a2 * a5 * a6 + 4 * a2 * a6
          + a3 * a4 * a6 + 4 * a3 * a4
          + a3 * a5 * a6 + 4 * a3 * a5
          + 4 * a4 * a6 + 4 * a5 * a6 := by
    rw [deltaX, hx1_offset, hx2_offset, hx3_offset, hx4_offset, hx5_offset, hx6_offset]
    ring
  have hdelta_ge_128 : 128 ≤ deltaX x1 x2 x3 x4 x5 x6 := by
    rw [hdelta_split]
    have hfour_nonneg : (0 : ℝ) ≤ 4 := by norm_num
    have ht1 : 0 ≤ a1 * (16 - 4 * a1 - a1 * a4) :=
      mul_nonneg ha1_nonneg hb14
    have ht2 : 0 ≤ a4 * (16 - 4 * a4 - a1 * a4) :=
      mul_nonneg ha4_nonneg hb41
    have ht3 : 0 ≤ a2 * (16 - 4 * a2 - a2 * a5) :=
      mul_nonneg ha2_nonneg hb25
    have ht4 : 0 ≤ a5 * (16 - 4 * a5 - a2 * a5) :=
      mul_nonneg ha5_nonneg hb52
    have ht5 : 0 ≤ a3 * (16 - 4 * a3 - a3 * a6) :=
      mul_nonneg ha3_nonneg hb36
    have ht6 : 0 ≤ a6 * (16 - 4 * a6 - a3 * a6) :=
      mul_nonneg ha6_nonneg hb63
    have ht7 : 0 ≤ a1 * a2 * (4 - a6) :=
      mul_nonneg (mul_nonneg ha1_nonneg ha2_nonneg) h4a6
    have ht8 : 0 ≤ a1 * a3 * (4 - a5) :=
      mul_nonneg (mul_nonneg ha1_nonneg ha3_nonneg) h4a5
    have ht9 : 0 ≤ a4 * a2 * (4 - a3) :=
      mul_nonneg (mul_nonneg ha4_nonneg ha2_nonneg) h4a3
    have ht10 : 0 ≤ a4 * a5 * (4 - a6) :=
      mul_nonneg (mul_nonneg ha4_nonneg ha5_nonneg) h4a6
    have ht11 : 0 ≤ a1 * a2 * a4 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha2_nonneg) ha4_nonneg
    have ht12 : 0 ≤ a1 * a2 * a5 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha2_nonneg) ha5_nonneg
    have ht13 : 0 ≤ a1 * a3 * a4 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha3_nonneg) ha4_nonneg
    have ht14 : 0 ≤ a1 * a3 * a6 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha3_nonneg) ha6_nonneg
    have ht15 : 0 ≤ a1 * a4 * a5 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha4_nonneg) ha5_nonneg
    have ht16 : 0 ≤ a1 * a4 * a6 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha4_nonneg) ha6_nonneg
    have ht17 : 0 ≤ 4 * a1 * a5 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha1_nonneg) ha5_nonneg
    have ht18 : 0 ≤ 4 * a1 * a6 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha1_nonneg) ha6_nonneg
    have ht19 : 0 ≤ a2 * a3 * a5 :=
      mul_nonneg (mul_nonneg ha2_nonneg ha3_nonneg) ha5_nonneg
    have ht20 : 0 ≤ a2 * a3 * a6 :=
      mul_nonneg (mul_nonneg ha2_nonneg ha3_nonneg) ha6_nonneg
    have ht21 : 0 ≤ 4 * a2 * a3 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha2_nonneg) ha3_nonneg
    have ht22 : 0 ≤ a2 * a4 * a5 :=
      mul_nonneg (mul_nonneg ha2_nonneg ha4_nonneg) ha5_nonneg
    have ht23 : 0 ≤ a2 * a5 * a6 :=
      mul_nonneg (mul_nonneg ha2_nonneg ha5_nonneg) ha6_nonneg
    have ht24 : 0 ≤ 4 * a2 * a6 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha2_nonneg) ha6_nonneg
    have ht25 : 0 ≤ a3 * a4 * a6 :=
      mul_nonneg (mul_nonneg ha3_nonneg ha4_nonneg) ha6_nonneg
    have ht26 : 0 ≤ 4 * a3 * a4 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha3_nonneg) ha4_nonneg
    have ht27 : 0 ≤ a3 * a5 * a6 :=
      mul_nonneg (mul_nonneg ha3_nonneg ha5_nonneg) ha6_nonneg
    have ht28 : 0 ≤ 4 * a3 * a5 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha3_nonneg) ha5_nonneg
    have ht29 : 0 ≤ 4 * a4 * a6 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha4_nonneg) ha6_nonneg
    have ht30 : 0 ≤ 4 * a5 * a6 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha5_nonneg) ha6_nonneg
    linarith
  have hdelta_pos : 0 < deltaX x1 x2 x3 x4 x5 x6 := by
    nlinarith [hdelta_ge_128]
  have hsqrt_arg_pos :
      0 < 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by
    nlinarith [hx1_pos, hdelta_pos]
  have hx1_ge_four : (4 : ℝ) ≤ x1 := by
    norm_num at hx1_lo ⊢
    exact hx1_lo
  have hprod_ge_512 :
      (4 : ℝ) * 128 ≤ x1 * deltaX x1 x2 x3 x4 x5 x6 := by
    exact mul_le_mul hx1_ge_four hdelta_ge_128 (by norm_num) hx1_nonneg
  have hsqrt_arg_ge_2048 :
      (2048 : ℝ) ≤ 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by
    calc
      (2048 : ℝ) = 4 * ((4 : ℝ) * 128) := by norm_num
      _ ≤ 4 * (x1 * deltaX x1 x2 x3 x4 x5 x6) := by
        exact mul_le_mul_of_nonneg_left hprod_ge_512 (by norm_num)
      _ = 4 * x1 * deltaX x1 x2 x3 x4 x5 x6 := by ring
  have hsqrt_ge_45 :
      (45 : ℝ) ≤ Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [hsqrt_arg_ge_2048]
  have hsqrt_pos :
      0 < Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6) := by
    nlinarith [hsqrt_ge_45]
  have hdih_expand :
      dihX x1 x2 x3 x4 x5 x6 =
        Real.pi / 2
          + Real.arctan
            ((-deltaX4 x1 x2 x3 x4 x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)) := by
    rfl
  have hneg_deltaX4_split :
      -deltaX4 x1 x2 x3 x4 x5 x6 =
        a1 ^ 2 - a1 * a2 - a1 * a3 + 2 * a1 * a4
          - a1 * a5 - a1 * a6 + a2 * a3 - a2 * a5
          - 4 * a2 - a3 * a6 - 4 * a3 + 8 * a4
          + a5 * a6 - 4 * a5 - 4 * a6 - 16 := by
    rw [deltaX4, hx1_offset, hx2_offset, hx3_offset, hx4_offset, hx5_offset, hx6_offset]
    ring
  have hneg_deltaX4_grouped :
      -deltaX4 x1 x2 x3 x4 x5 x6 =
        (a1 ^ 2 + 2 * a1 * a4 + 8 * a4 - 16)
          + (a2 * a3 - a1 * a2 - a1 * a3 - 4 * a2 - 4 * a3)
          + (a5 * a6 - a1 * a5 - a1 * a6 - 4 * a5 - 4 * a6)
          - a2 * a5 - a3 * a6 := by
    rw [hneg_deltaX4_split]
    ring
  have hdeltaX4_core_le_20 :
      a1 ^ 2 + 2 * a1 * a4 + 8 * a4 - 16 ≤ 20 :=
    offset_deltaX4_core_le_twenty ha1_nonneg ha1_hi ha4_nonneg ha4_hi
  have hdeltaX4_23_nonpos :
      a2 * a3 - a1 * a2 - a1 * a3 - 4 * a2 - 4 * a3 ≤ 0 := by
    have ha2_gap : 0 ≤ a2 * (4 - a3) :=
      mul_nonneg ha2_nonneg h4a3
    have ha1a2_nonneg : 0 ≤ a1 * a2 :=
      mul_nonneg ha1_nonneg ha2_nonneg
    have ha1a3_nonneg : 0 ≤ a1 * a3 :=
      mul_nonneg ha1_nonneg ha3_nonneg
    nlinarith only [ha2_gap, ha1a2_nonneg, ha1a3_nonneg, ha3_nonneg]
  have hdeltaX4_56_nonpos :
      a5 * a6 - a1 * a5 - a1 * a6 - 4 * a5 - 4 * a6 ≤ 0 := by
    have ha5_gap : 0 ≤ a5 * (4 - a6) :=
      mul_nonneg ha5_nonneg h4a6
    have ha1a5_nonneg : 0 ≤ a1 * a5 :=
      mul_nonneg ha1_nonneg ha5_nonneg
    have ha1a6_nonneg : 0 ≤ a1 * a6 :=
      mul_nonneg ha1_nonneg ha6_nonneg
    nlinarith only [ha5_gap, ha1a5_nonneg, ha1a6_nonneg, ha6_nonneg]
  have hdeltaX4_cross_nonpos : -a2 * a5 - a3 * a6 ≤ 0 := by
    have ha2a5_nonneg : 0 ≤ a2 * a5 :=
      mul_nonneg ha2_nonneg ha5_nonneg
    have ha3a6_nonneg : 0 ≤ a3 * a6 :=
      mul_nonneg ha3_nonneg ha6_nonneg
    nlinarith only [ha2a5_nonneg, ha3a6_nonneg]
  have hneg_deltaX4_le_20 :
      -deltaX4 x1 x2 x3 x4 x5 x6 ≤ 20 := by
    rw [hneg_deltaX4_grouped]
    linarith only
      [hdeltaX4_core_le_20, hdeltaX4_23_nonpos,
        hdeltaX4_56_nonpos, hdeltaX4_cross_nonpos]
  have hatn_ratio_le_four_ninth :
      (-deltaX4 x1 x2 x3 x4 x5 x6)
          / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
        ≤ 4 / 9 := by
    rw [div_le_iff₀ hsqrt_pos]
    nlinarith only [hneg_deltaX4_le_20, hsqrt_ge_45]
  have hatn_ratio_arctan_le_four_ninth :
      Real.arctan
          ((-deltaX4 x1 x2 x3 x4 x5 x6)
            / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
        ≤ Real.arctan (4 / 9) := by
    exact Real.arctan_mono hatn_ratio_le_four_ninth
  have hdih_le_pi_half_plus_atn_four_ninth :
      dihX x1 x2 x3 x4 x5 x6
        ≤ Real.pi / 2 + Real.arctan (4 / 9) := by
    rw [hdih_expand]
    linarith only [hatn_ratio_arctan_le_four_ninth]
  have hsharp_ratio_suffices :
      (-deltaX4 x1 x2 x3 x4 x5 x6)
          / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6)
        ≤ 1 / 3 →
        dihX x1 x2 x3 x4 x5 x6 < 1.893 := by
    intro hratio_le_one_third
    have hatn_ratio_arctan_le_one_third :
        Real.arctan
            ((-deltaX4 x1 x2 x3 x4 x5 x6)
              / Real.sqrt (4 * x1 * deltaX x1 x2 x3 x4 x5 x6))
          ≤ Real.arctan (1 / 3) := by
      exact Real.arctan_mono hratio_le_one_third
    have hdih_le_pi_half_plus_atn_one_third :
        dihX x1 x2 x3 x4 x5 x6
          ≤ Real.pi / 2 + Real.arctan (1 / 3) := by
      rw [hdih_expand]
      linarith only [hatn_ratio_arctan_le_one_third]
    exact lt_of_le_of_lt
      hdih_le_pi_half_plus_atn_one_third
      pi_half_add_arctan_one_third_lt_1893
  have hsharp_square_suffices :
      (0 ≤ -deltaX4 x1 x2 x3 x4 x5 x6 →
        9 * (-deltaX4 x1 x2 x3 x4 x5 x6) ^ 2
          ≤ 4 * x1 * deltaX x1 x2 x3 x4 x5 x6) →
        dihX x1 x2 x3 x4 x5 x6 < 1.893 := by
    intro hquad_nonneg_case
    apply hsharp_ratio_suffices
    exact ratio_le_one_third_of_sq_le_nonneg_case
      hsqrt_arg_pos hsqrt_pos hquad_nonneg_case
  have htarget_iff :
      dihX x1 x2 x3 x4 x5 x6 + (-1.893) < 0 ↔
        dihX x1 x2 x3 x4 x5 x6 < 1.893 := by
    constructor <;> intro h <;> linarith
  let dOff : ℝ :=
    128
      + a1 * (16 - 4 * a1 - a1 * a4)
      + a4 * (16 - 4 * a4 - a1 * a4)
      + a2 * (16 - 4 * a2 - a2 * a5)
      + a5 * (16 - 4 * a5 - a2 * a5)
      + a3 * (16 - 4 * a3 - a3 * a6)
      + a6 * (16 - 4 * a6 - a3 * a6)
      + a1 * a2 * (4 - a6)
      + a1 * a3 * (4 - a5)
      + a4 * a2 * (4 - a3)
      + a4 * a5 * (4 - a6)
      + a1 * a2 * a4 + a1 * a2 * a5
      + a1 * a3 * a4 + a1 * a3 * a6
      + a1 * a4 * a5 + a1 * a4 * a6
      + 4 * a1 * a5 + 4 * a1 * a6
      + a2 * a3 * a5 + a2 * a3 * a6
      + 4 * a2 * a3 + a2 * a4 * a5
      + a2 * a5 * a6 + 4 * a2 * a6
      + a3 * a4 * a6 + 4 * a3 * a4
      + a3 * a5 * a6 + 4 * a3 * a5
      + 4 * a4 * a6 + 4 * a5 * a6
  let nOff : ℝ :=
    a1 ^ 2 - a1 * a2 - a1 * a3 + 2 * a1 * a4
      - a1 * a5 - a1 * a6 + a2 * a3 - a2 * a5
      - 4 * a2 - a3 * a6 - 4 * a3 + 8 * a4
      + a5 * a6 - 4 * a5 - 4 * a6 - 16
  have hsharp_offset_poly_suffices :
      (0 ≤ -deltaX4 x1 x2 x3 x4 x5 x6 →
        0 ≤ 4 * (a1 + 4) * dOff - 9 * nOff ^ 2) →
        dihX x1 x2 x3 x4 x5 x6 < 1.893 := by
    intro hpoly_nonneg_case
    apply hsharp_square_suffices
    intro hN_nonneg
    have hpoly_nonneg : 0 ≤ 4 * (a1 + 4) * dOff - 9 * nOff ^ 2 :=
      hpoly_nonneg_case hN_nonneg
    rw [hneg_deltaX4_split, hdelta_split, hx1_offset]
    change 9 * nOff ^ 2 ≤ 4 * (a1 + 4) * dOff
    nlinarith only [hpoly_nonneg]
  rw [htarget_iff]
  apply hsharp_offset_poly_suffices
  intro hN_nonneg
  -- Record the sign hypothesis on the shifted numerator polynomial.
  have hnOff_nonneg : 0 ≤ nOff := by
    dsimp [nOff]
    rw [← hneg_deltaX4_split]
    exact hN_nonneg
  -- The cross terms of the numerator never increase the pair (a1,a4) term.
  have htail_nonpos :
      a2 * a3 - a1 * a2 - a1 * a3 - a2 * a5 - 4 * a2
        - a3 * a6 - 4 * a3 - a1 * a5 - a1 * a6
        + a5 * a6 - 4 * a5 - 4 * a6 ≤ 0 :=
    offset_tail_term_nonpos
      ha1_nonneg ha2_nonneg ha3_nonneg ha3_hi
      ha5_nonneg ha6_nonneg ha6_hi
  have hnOff_le_pair :
      nOff ≤ a1 ^ 2 + 2 * a1 * a4 + 8 * a4 - 16 := by
    have hnOff_tail_eq :
        nOff = (a1 ^ 2 + 2 * a1 * a4 + 8 * a4 - 16)
          + (a2 * a3 - a1 * a2 - a1 * a3 - a2 * a5 - 4 * a2
              - a3 * a6 - 4 * a3 - a1 * a5 - a1 * a6
              + a5 * a6 - 4 * a5 - 4 * a6) := by
      dsimp [nOff]
      ring
    rw [hnOff_tail_eq]
    nlinarith only [htail_nonpos]
  have hpair_nonneg : 0 ≤ a1 ^ 2 + 2 * a1 * a4 + 8 * a4 - 16 := by
    nlinarith only [hnOff_le_pair, hnOff_nonneg]
  have hsq_bound :
      nOff ^ 2 ≤ (a1 ^ 2 + 2 * a1 * a4 + 8 * a4 - 16) ^ 2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg hnOff_nonneg,
      abs_of_nonneg hpair_nonneg]
    exact hnOff_le_pair
  -- The shifted delta is at least the two-variable pair part.
  have hdOff_ge_pair :
      128 + a1 * (16 - 4 * a1 - a1 * a4)
        + a4 * (16 - 4 * a4 - a1 * a4) ≤ dOff := by
    have hfour_nonneg : (0 : ℝ) ≤ 4 := by norm_num
    have ht3 : 0 ≤ a2 * (16 - 4 * a2 - a2 * a5) :=
      mul_nonneg ha2_nonneg hb25
    have ht4 : 0 ≤ a5 * (16 - 4 * a5 - a2 * a5) :=
      mul_nonneg ha5_nonneg hb52
    have ht5 : 0 ≤ a3 * (16 - 4 * a3 - a3 * a6) :=
      mul_nonneg ha3_nonneg hb36
    have ht6 : 0 ≤ a6 * (16 - 4 * a6 - a3 * a6) :=
      mul_nonneg ha6_nonneg hb63
    have ht7 : 0 ≤ a1 * a2 * (4 - a6) :=
      mul_nonneg (mul_nonneg ha1_nonneg ha2_nonneg) h4a6
    have ht8 : 0 ≤ a1 * a3 * (4 - a5) :=
      mul_nonneg (mul_nonneg ha1_nonneg ha3_nonneg) h4a5
    have ht9 : 0 ≤ a4 * a2 * (4 - a3) :=
      mul_nonneg (mul_nonneg ha4_nonneg ha2_nonneg) h4a3
    have ht10 : 0 ≤ a4 * a5 * (4 - a6) :=
      mul_nonneg (mul_nonneg ha4_nonneg ha5_nonneg) h4a6
    have ht11 : 0 ≤ a1 * a2 * a4 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha2_nonneg) ha4_nonneg
    have ht12 : 0 ≤ a1 * a2 * a5 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha2_nonneg) ha5_nonneg
    have ht13 : 0 ≤ a1 * a3 * a4 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha3_nonneg) ha4_nonneg
    have ht14 : 0 ≤ a1 * a3 * a6 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha3_nonneg) ha6_nonneg
    have ht15 : 0 ≤ a1 * a4 * a5 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha4_nonneg) ha5_nonneg
    have ht16 : 0 ≤ a1 * a4 * a6 :=
      mul_nonneg (mul_nonneg ha1_nonneg ha4_nonneg) ha6_nonneg
    have ht17 : 0 ≤ 4 * a1 * a5 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha1_nonneg) ha5_nonneg
    have ht18 : 0 ≤ 4 * a1 * a6 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha1_nonneg) ha6_nonneg
    have ht19 : 0 ≤ a2 * a3 * a5 :=
      mul_nonneg (mul_nonneg ha2_nonneg ha3_nonneg) ha5_nonneg
    have ht20 : 0 ≤ a2 * a3 * a6 :=
      mul_nonneg (mul_nonneg ha2_nonneg ha3_nonneg) ha6_nonneg
    have ht21 : 0 ≤ 4 * a2 * a3 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha2_nonneg) ha3_nonneg
    have ht22 : 0 ≤ a2 * a4 * a5 :=
      mul_nonneg (mul_nonneg ha2_nonneg ha4_nonneg) ha5_nonneg
    have ht23 : 0 ≤ a2 * a5 * a6 :=
      mul_nonneg (mul_nonneg ha2_nonneg ha5_nonneg) ha6_nonneg
    have ht24 : 0 ≤ 4 * a2 * a6 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha2_nonneg) ha6_nonneg
    have ht25 : 0 ≤ a3 * a4 * a6 :=
      mul_nonneg (mul_nonneg ha3_nonneg ha4_nonneg) ha6_nonneg
    have ht26 : 0 ≤ 4 * a3 * a4 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha3_nonneg) ha4_nonneg
    have ht27 : 0 ≤ a3 * a5 * a6 :=
      mul_nonneg (mul_nonneg ha3_nonneg ha5_nonneg) ha6_nonneg
    have ht28 : 0 ≤ 4 * a3 * a5 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha3_nonneg) ha5_nonneg
    have ht29 : 0 ≤ 4 * a4 * a6 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha4_nonneg) ha6_nonneg
    have ht30 : 0 ≤ 4 * a5 * a6 :=
      mul_nonneg (mul_nonneg hfour_nonneg ha5_nonneg) ha6_nonneg
    have hg1 :
        0 ≤ a2 * (16 - 4 * a2 - a2 * a5)
          + a5 * (16 - 4 * a5 - a2 * a5)
          + a3 * (16 - 4 * a3 - a3 * a6)
          + a6 * (16 - 4 * a6 - a3 * a6) := by
      nlinarith only [ht3, ht4, ht5, ht6]
    have hg2 :
        0 ≤ a1 * a2 * (4 - a6)
          + a1 * a3 * (4 - a5)
          + a4 * a2 * (4 - a3)
          + a4 * a5 * (4 - a6) := by
      nlinarith only [ht7, ht8, ht9, ht10]
    have hg3 :
        0 ≤ a1 * a2 * a4 + a1 * a2 * a5
          + a1 * a3 * a4 + a1 * a3 * a6
          + a1 * a4 * a5 + a1 * a4 * a6
          + 4 * a1 * a5 + 4 * a1 * a6 := by
      nlinarith only [ht11, ht12, ht13, ht14, ht15, ht16, ht17, ht18]
    have hg4 :
        0 ≤ a2 * a3 * a5 + a2 * a3 * a6
          + 4 * a2 * a3 + a2 * a4 * a5
          + a2 * a5 * a6 + 4 * a2 * a6
          + a3 * a4 * a6 + 4 * a3 * a4 := by
      nlinarith only [ht19, ht20, ht21, ht22, ht23, ht24, ht25, ht26]
    have hg5 :
        0 ≤ a3 * a5 * a6 + 4 * a3 * a5
          + 4 * a4 * a6 + 4 * a5 * a6 := by
      nlinarith only [ht27, ht28, ht29, ht30]
    have htail_sum :
        dOff
          - (128 + a1 * (16 - 4 * a1 - a1 * a4)
              + a4 * (16 - 4 * a4 - a1 * a4))
          = (a2 * (16 - 4 * a2 - a2 * a5)
              + a5 * (16 - 4 * a5 - a2 * a5)
              + a3 * (16 - 4 * a3 - a3 * a6)
              + a6 * (16 - 4 * a6 - a3 * a6))
            + (a1 * a2 * (4 - a6)
              + a1 * a3 * (4 - a5)
              + a4 * a2 * (4 - a3)
              + a4 * a5 * (4 - a6))
            + (a1 * a2 * a4 + a1 * a2 * a5
              + a1 * a3 * a4 + a1 * a3 * a6
              + a1 * a4 * a5 + a1 * a4 * a6
              + 4 * a1 * a5 + 4 * a1 * a6)
            + (a2 * a3 * a5 + a2 * a3 * a6
              + 4 * a2 * a3 + a2 * a4 * a5
              + a2 * a5 * a6 + 4 * a2 * a6
              + a3 * a4 * a6 + 4 * a3 * a4)
            + (a3 * a5 * a6 + 4 * a3 * a5
              + 4 * a4 * a6 + 4 * a5 * a6) := by
      dsimp [dOff]
      ring
    have htail : 0 ≤ dOff
        - (128 + a1 * (16 - 4 * a1 - a1 * a4)
            + a4 * (16 - 4 * a4 - a1 * a4)) := by
      rw [htail_sum]
      nlinarith only [hg1, hg2, hg3, hg4, hg5]
    nlinarith only [htail]
  -- Numerical certificate for the pair part of the remaining obligation.
  have hcert :
      0 ≤ 4 * (a1 + 4)
            * (128 + 16 * a1 - 4 * a1 ^ 2 - a1 ^ 2 * a4
                + 16 * a4 - 4 * a4 ^ 2 - a1 * a4 ^ 2)
        - 9 * (a1 ^ 2 + 2 * a1 * a4 + 8 * a4 - 16) ^ 2 :=
    pair_shift_quad_nonneg
      ha1_nonneg ha1_hi ha4_hi hpair_nonneg
  have hB_le_pairD :
      9 * (a1 ^ 2 + 2 * a1 * a4 + 8 * a4 - 16) ^ 2
        ≤ 4 * (a1 + 4)
            * (128 + a1 * (16 - 4 * a1 - a1 * a4)
              + a4 * (16 - 4 * a4 - a1 * a4)) := by
    have hD_form :
        128 + 16 * a1 - 4 * a1 ^ 2 - a1 ^ 2 * a4
          + 16 * a4 - 4 * a4 ^ 2 - a1 * a4 ^ 2
          = 128 + a1 * (16 - 4 * a1 - a1 * a4)
            + a4 * (16 - 4 * a4 - a1 * a4) := by
      ring
    nlinarith only [hcert, hD_form]
  have hnine_n : 9 * nOff ^ 2
      ≤ 9 * (a1 ^ 2 + 2 * a1 * a4 + 8 * a4 - 16) ^ 2 := by
    nlinarith only [hsq_bound]
  have hrhs_mono :
      4 * (a1 + 4)
            * (128 + a1 * (16 - 4 * a1 - a1 * a4)
              + a4 * (16 - 4 * a4 - a1 * a4))
        ≤ 4 * (a1 + 4) * dOff := by
    have hpos : 0 ≤ 4 * (a1 + 4) := by positivity
    exact mul_le_mul_of_nonneg_left hdOff_ge_pair hpos
  have hfinal :
      9 * nOff ^ 2 ≤ 4 * (a1 + 4) * dOff := by
    exact le_trans hnine_n (le_trans hB_le_pairD hrhs_mono)
  nlinarith only [hfinal]
