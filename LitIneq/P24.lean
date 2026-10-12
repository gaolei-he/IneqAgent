import Mathlib

set_option linter.style.header false
set_option linter.unusedVariables false

set_option maxHeartbeats 8000000

namespace Leanpro.BoxJsonlWithSources

/-
dataset_index: 24
id: A04
name: Cap 4
source_status: confirmed_transformed
paper_title: An efficient algorithm for range computation of polynomials using the Bernstein form
paper_url: https://doi.org/10.1007/s10898-008-9382-y
original_f: -x1*x3^3 + 4*x2*x3^2*x4 + 4*x1*x3*x4^2 + 2*x2*x4^3 + 4*x1*x3 + 4*x3^2 - 10*x2*x4 - 10*x4^2 + 2 + 31800966258/10000000000
source_evidence: PDF DOI 10.1007/s10898-008-9382-y; Table 1 Ex 4; Appendix A Problem 4

The polynomial and constraints preserve the source expression and order.
The theorem constant uses the z3_adjustment above for an exact inequality.
-/
set_option maxHeartbeats 4000000 in
lemma cap4_cubic (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ u^3 + 10*u^2 - 5*u
        + 2*(5180096625844998335319568973991 / 1000000000000000000000000000000 - 39/8 : ℝ) := by
  set s : ℝ := Real.sqrt 115 with hsdef
  have hs : s^2 = 115 := by rw [hsdef]; exact Real.sq_sqrt (by norm_num)
  have hsnn : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg 115
  have h10 : (10:ℝ) ≤ s := by
    rw [hsdef, ← Real.sqrt_sq (show (0:ℝ) ≤ 10 by norm_num)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have key : u^3 + 10*u^2 - 5*u
        + 2*(5180096625844998335319568973991 / 1000000000000000000000000000000 - 39/8 : ℝ)
      = (u - (s-10)/3)^2 * (u + 10 + 2*((s-10)/3))
        + (2/27)*(27*(5180096625844998335319568973991 / 1000000000000000000000000000000 - 39/8) + 1225 - 115*s) := by
    nlinarith [hs]
  rw [key]
  have hsq : (0:ℝ) ≤ (u - (s-10)/3)^2 := sq_nonneg _
  have hfac : 0 ≤ u + 10 + 2*((s-10)/3) := by nlinarith [h10, hu]
  have hconst : 0 ≤ (2/27)*(27*(5180096625844998335319568973991 / 1000000000000000000000000000000 - 39/8) + 1225 - 115*s) := by
    have hle : s^2 ≤ ((27*(5180096625844998335319568973991 / 1000000000000000000000000000000 - 39/8) + 1225)/115)^2 := by
      rw [hs]; norm_num
    have hTnn : 0 ≤ (27*(5180096625844998335319568973991 / 1000000000000000000000000000000 - 39/8) + 1225)/115 := by norm_num
    have hT : s ≤ (27*(5180096625844998335319568973991 / 1000000000000000000000000000000 - 39/8) + 1225)/115 := by
      nlinarith [hsnn, hle, hTnn, sq_nonneg (s - (27*(5180096625844998335319568973991 / 1000000000000000000000000000000 - 39/8) + 1225)/115)]
    nlinarith [hT]
  nlinarith [mul_nonneg hsq hfac]

theorem box_benchmark_24_a04_cap_4 :
    ∀ x1 x2 x3 x4 : ℝ,
      (-1 / 2 : ℝ) <= x1 ∧
      x1 <= (1 / 2 : ℝ) ∧
      (-1 / 2 : ℝ) <= x2 ∧
      x2 <= (1 / 2 : ℝ) ∧
      (-1 / 2 : ℝ) <= x3 ∧
      x3 <= (1 / 2 : ℝ) ∧
      (-1 / 2 : ℝ) <= x4 ∧
      x4 <= (1 / 2 : ℝ) →
        0 <= (5180096625844998335319568973991 / 1000000000000000000000000000000 : ℝ) - 10*x4^2 + 4*x3^2 - 1*x1*x3^3 - 10*x2*x4 + 2*x2*x4^3 + 4*x1*x3 + 4*x1*x3*x4^2 + 4*x2*x4*x3^2 := by
  intro x1 x2 x3 x4 h
  obtain ⟨hx1l, hx1u, hx2l, hx2u, hx3l, hx3u, hx4l, hx4u⟩ := h
  have hx1a : |x1| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx2a : |x2| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx3a : |x3| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx4a : |x4| ≤ 1/2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hx3sq : x3^2 ≤ 1/4 := by
    have h1 : 0 ≤ 1/2 - x3 := by linarith
    have h2 : 0 ≤ 1/2 + x3 := by linarith
    nlinarith [mul_nonneg h1 h2]
  have hx4sq : x4^2 ≤ 1/4 := by
    have h1 : 0 ≤ 1/2 - x4 := by linarith
    have h2 : 0 ≤ 1/2 + x4 := by linarith
    nlinarith [mul_nonneg h1 h2]
  set u := |x3| with hudef
  set v := |x4| with hvdef
  have hu2 : u^2 = x3^2 := by rw [hudef]; exact sq_abs x3
  have hv2 : v^2 = x4^2 := by rw [hvdef]; exact sq_abs x4
  have hu_nn : 0 ≤ u := by rw [hudef]; exact abs_nonneg x3
  have hv_nn : 0 ≤ v := by rw [hvdef]; exact abs_nonneg x4
  have hu_le : u ≤ 1/2 := by rw [hudef]; exact hx3a
  have hv_le : v ≤ 1/2 := by rw [hvdef]; exact hx4a
  have hP : 0 < 4 + 4*x4^2 - x3^2 := by nlinarith [hx3sq, sq_nonneg x4]
  have hR : 0 < 10 - 2*x4^2 - 4*x3^2 := by nlinarith [hx4sq, hx3sq]
  have hx1x3 : 0 ≤ x1*x3 + (1/2)*u := by
    have hle : |x1| * |x3| ≤ (1/2) * u := by
      rw [hudef]
      simpa using mul_le_mul_of_nonneg_right hx1a (abs_nonneg x3)
    have hna := neg_abs_le (x1*x3)
    rw [abs_mul] at hna
    linarith
  have hx2x4 : 0 ≤ (1/2)*v - x2*x4 := by
    have hle : |x2| * |x4| ≤ (1/2) * v := by
      rw [hvdef]
      simpa using mul_le_mul_of_nonneg_right hx2a (abs_nonneg x4)
    have hna := le_abs_self (x2*x4)
    rw [abs_mul] at hna
    linarith
  let F : ℝ → ℝ → ℝ := fun a b => (5180096625844998335319568973991 / 1000000000000000000000000000000 : ℝ) - 10*b^2 + 4*a^2 - (1/2)*a*(4+4*b^2-a^2) - (1/2)*b*(10-2*b^2-4*a^2)
  have hle : F u v ≤ (5180096625844998335319568973991 / 1000000000000000000000000000000 : ℝ) - 10*x4^2 + 4*x3^2 - 1*x1*x3^3 - 10*x2*x4 + 2*x2*x4^3 + 4*x1*x3 + 4*x1*x3*x4^2 + 4*x2*x4*x3^2 := by
    have hkey : (5180096625844998335319568973991 / 1000000000000000000000000000000 : ℝ) - 10*x4^2 + 4*x3^2 - 1*x1*x3^3 - 10*x2*x4 + 2*x2*x4^3 + 4*x1*x3 + 4*x1*x3*x4^2 + 4*x2*x4*x3^2
        = F u v + (x1*x3 + (1/2)*u)*(4+4*x4^2-x3^2) + ((1/2)*v - x2*x4)*(10-2*x4^2-4*x3^2) := by
      dsimp only [F]; rw [hu2, hv2]; ring
    rw [hkey]
    have t1 : 0 ≤ (x1*x3 + (1/2)*u)*(4+4*x4^2-x3^2) := mul_nonneg hx1x3 (le_of_lt hP)
    have t2 : 0 ≤ ((1/2)*v - x2*x4)*(10-2*x4^2-4*x3^2) := mul_nonneg hx2x4 (le_of_lt hR)
    linarith
  have hFnn : 0 ≤ F u v := by
    have hvv : v^2 ≤ 1/4 := by rw [hv2]; exact hx4sq
    have hu2u : 2*u^2 - u ≤ 0 := by
      have h : u*(2*u-1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hu_nn (by linarith [hu_le])
      nlinarith [h]
    have hterm : 0 ≤ (2*u + 19/2)*v := mul_nonneg (by linarith [hu_nn]) hv_nn
    have hB : v^2 - (2*u+19/2)*v + 2*u^2 - u - 39/4 ≤ 0 := by nlinarith [hvv, hterm, hu2u]
    have hfac : F u v - F u (1/2) = (v - 1/2)*(v^2 - (2*u+19/2)*v + 2*u^2 - u - 39/4) := by
      dsimp only [F]; ring
    have hge : F u (1/2) ≤ F u v := by
      have hp : 0 ≤ (v-1/2)*(v^2 - (2*u+19/2)*v + 2*u^2 - u - 39/4) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith [hv_le]) hB
      linarith [hfac, hp]
    have hhalf : 0 ≤ F u (1/2) := by
      have hcub := cap4_cubic u hu_nn
      have heq : F u (1/2) = (1/2)*(u^3 + 10*u^2 - 5*u + 2*(5180096625844998335319568973991 / 1000000000000000000000000000000 - 39/8 : ℝ)) := by
        dsimp only [F]; ring
      rw [heq]; linarith [hcub]
    linarith [hge, hhalf]
  linarith
