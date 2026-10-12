import Mathlib

namespace Leanpro.MetiTarskiExamplesSplit

theorem ajn :
    ∀ sx sy vx vy nvx nvy nwx nwy eps pt px : ℝ,
      px > 0 ∧ pt > 0 ∧ (eps = 1 ∨ eps = -1)
      ∧ nvx * sx + nvy * sy + nvx * nvx * pt + nvy * nvy * pt ≥ 0
      ∧ sx * vx + sy * vy < 0
      ∧ sx * vy * eps - sy * vx * eps ≤ 0
      ∧ nvy * sx * eps - nvx * sy * eps < 0
      ∧ nvx * vy * eps - nvy * vx * eps < 0
      ∧ nvy * sx * eps - nvx * sy * eps ≤ 0
      ∧ -1 * (nwx * sy * eps) - nvy * nwx * eps * pt
        + nwy * sx * eps + nvx * nwy * eps * pt < 0
      ∧ nwx * sx + nwy * sy + nvx * nwx * pt + nvy * nwy * pt
        > nvx * sx + nvy * sy + nvx * nvx * pt + nvy * nvy * pt
      ∧ nwx * vy * eps - nwy * vx * eps < 0 →
        -1 * (nvx * sy * eps * pt) - nwx * sy * eps * px
        + nvy * sx * eps * pt + nwy * sx * eps * px < 0 := by
  intro sx sy vx vy nvx nvy nwx nwy eps pt px h
  rcases h with
    ⟨hpx_pos, hpt_pos, heps, hnv_dot_u_nonneg, hs_dot_v_neg,
      hs_cross_v_nonpos, hnv_cross_s_neg, hnv_cross_v_neg,
      hnv_cross_s_nonpos, hnw_cross_u_neg, hnw_dot_u_gt,
      hnw_cross_v_neg⟩
  have hpx_nonneg : 0 ≤ px := le_of_lt hpx_pos
  have hpt_nonneg : 0 ≤ pt := le_of_lt hpt_pos
  have heps_sq : eps * eps = 1 := by
    rcases heps with rfl | rfl <;> norm_num
  have hnv_dot_shift_nonneg :
      nvx * (sx + nvx * pt) + nvy * (sy + nvy * pt) ≥ 0 := by
    nlinarith [hnv_dot_u_nonneg]
  have hnw_dot_shift_gt :
      nwx * (sx + nvx * pt) + nwy * (sy + nvy * pt)
        > nvx * (sx + nvx * pt) + nvy * (sy + nvy * pt) := by
    nlinarith [hnw_dot_u_gt]
  have hnv_cross_shift_neg :
      nvy * (sx + nvx * pt) * eps - nvx * (sy + nvy * pt) * eps < 0 := by
    nlinarith [hnv_cross_s_neg]
  have hnv_cross_shift_nonpos :
      nvy * (sx + nvx * pt) * eps - nvx * (sy + nvy * pt) * eps ≤ 0 := by
    nlinarith [hnv_cross_s_nonpos]
  have hnw_cross_shift_neg :
      nwy * (sx + nvx * pt) * eps - nwx * (sy + nvy * pt) * eps < 0 := by
    nlinarith [hnw_cross_u_neg]
  have hnv_pt_cross_neg :
      pt * (nvy * sx * eps - nvx * sy * eps) < 0 := by
    exact mul_neg_of_pos_of_neg hpt_pos hnv_cross_s_neg
  have hgoal_decomp :
      -1 * (nvx * sy * eps * pt) - nwx * sy * eps * px
          + nvy * sx * eps * pt + nwy * sx * eps * px
        =
        pt * (nvy * sx * eps - nvx * sy * eps)
          + px * (nwy * sx * eps - nwx * sy * eps) := by
    ring
  have hnv_goal_part_neg :
      -1 * (nvx * sy * eps * pt) + nvy * sx * eps * pt < 0 := by
    nlinarith [hnv_pt_cross_neg]
  have hgoal_of_nw_cross_s_neg :
      nwy * sx * eps - nwx * sy * eps < 0 →
        -1 * (nvx * sy * eps * pt) - nwx * sy * eps * px
          + nvy * sx * eps * pt + nwy * sx * eps * px < 0 := by
    intro hnw_cross_s_neg
    have hnw_px_cross_neg :
        px * (nwy * sx * eps - nwx * sy * eps) < 0 := by
      exact mul_neg_of_pos_of_neg hpx_pos hnw_cross_s_neg
    rw [hgoal_decomp]
    nlinarith [hnv_pt_cross_neg, hnw_px_cross_neg]
  have hgoal_of_nw_cross_s_nonpos :
      nwy * sx * eps - nwx * sy * eps ≤ 0 →
        -1 * (nvx * sy * eps * pt) - nwx * sy * eps * px
          + nvy * sx * eps * pt + nwy * sx * eps * px < 0 := by
    intro hnw_cross_s_nonpos
    have hnw_px_cross_nonpos :
        px * (nwy * sx * eps - nwx * sy * eps) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hpx_nonneg hnw_cross_s_nonpos
    rw [hgoal_decomp]
    nlinarith [hnv_pt_cross_neg, hnw_px_cross_nonpos]
  have hnw_cross_shift_decomp :
      -1 * (nwx * sy * eps) - nvy * nwx * eps * pt
          + nwy * sx * eps + nvx * nwy * eps * pt
        =
        (nwy * sx * eps - nwx * sy * eps)
          + pt * (nvx * nwy * eps - nvy * nwx * eps) := by
    ring
  have hnw_cross_s_neg_of_nv_nw_cross_nonneg :
      nvx * nwy * eps - nvy * nwx * eps ≥ 0 →
        nwy * sx * eps - nwx * sy * eps < 0 := by
    intro hnv_nw_cross_nonneg
    rw [hnw_cross_shift_decomp] at hnw_cross_u_neg
    have hpt_nv_nw_cross_nonneg :
        0 ≤ pt * (nvx * nwy * eps - nvy * nwx * eps) := by
      exact mul_nonneg hpt_nonneg hnv_nw_cross_nonneg
    nlinarith [hnw_cross_u_neg, hpt_nv_nw_cross_nonneg]
  have hgoal_of_nv_nw_cross_nonneg :
      nvx * nwy * eps - nvy * nwx * eps ≥ 0 →
        -1 * (nvx * sy * eps * pt) - nwx * sy * eps * px
          + nvy * sx * eps * pt + nwy * sx * eps * px < 0 := by
    intro hnv_nw_cross_nonneg
    exact hgoal_of_nw_cross_s_neg
      (hnw_cross_s_neg_of_nv_nw_cross_nonneg hnv_nw_cross_nonneg)
  have hcross_plucker :
      (nwy * sx * eps - nwx * sy * eps) * (nvx * vy * eps - nvy * vx * eps)
        = (nvy * sx * eps - nvx * sy * eps) * (nwx * vy * eps - nwy * vx * eps)
          + (sx * vy * eps - sy * vx * eps) * (nvx * nwy * eps - nvy * nwx * eps) := by
    nlinarith [heps_sq]
  have hnw_cross_s_neg :
      nwy * sx * eps - nwx * sy * eps < 0 := by
    by_cases hC_nonneg : 0 ≤ nvx * nwy * eps - nvy * nwx * eps
    · rw [hnw_cross_shift_decomp] at hnw_cross_u_neg
      have hpt_C_nonneg :
          0 ≤ pt * (nvx * nwy * eps - nvy * nwx * eps) := by
        exact mul_nonneg hpt_nonneg hC_nonneg
      have hpt_C_nonneg' :
          0 ≤ 0 + pt * (nvx * nwy * eps - nvy * nwx * eps) := by
        simpa using hpt_C_nonneg
      have hsum :
          nwy * sx * eps - nwx * sy * eps
            + pt * (nvx * nwy * eps - nvy * nwx * eps)
          < 0 + pt * (nvx * nwy * eps - nvy * nwx * eps) := by
        exact lt_of_lt_of_le hnw_cross_u_neg hpt_C_nonneg'
      simpa [add_comm, add_left_comm, add_assoc] using
        (lt_of_add_lt_add_right hsum)
    · have hC_neg : nvx * nwy * eps - nvy * nwx * eps < 0 := lt_of_not_ge hC_nonneg
      have hAF_pos :
          0 < (nvy * sx * eps - nvx * sy * eps) * (nwx * vy * eps - nwy * vx * eps) := by
        exact mul_pos_of_neg_of_neg hnv_cross_s_neg hnw_cross_v_neg
      have hDC_nonneg :
          0 ≤ (sx * vy * eps - sy * vx * eps) * (nvx * nwy * eps - nvy * nwx * eps) := by
        exact mul_nonneg_of_nonpos_of_nonpos hs_cross_v_nonpos (le_of_lt hC_neg)
      have hsum_pos :
          0 < (nvy * sx * eps - nvx * sy * eps) * (nwx * vy * eps - nwy * vx * eps)
            + (sx * vy * eps - sy * vx * eps) * (nvx * nwy * eps - nvy * nwx * eps) := by
        exact add_pos_of_pos_of_nonneg hAF_pos hDC_nonneg
      have hBE_pos :
          0 < (nwy * sx * eps - nwx * sy * eps) * (nvx * vy * eps - nvy * vx * eps) := by
        simpa [hcross_plucker, add_comm, add_left_comm, add_assoc] using hsum_pos
      have hnw_cross_s_neg' :
          nwy * sx * eps - nwx * sy * eps < 0 := by
        by_contra hnonneg
        have hnonneg' : 0 ≤ nwy * sx * eps - nwx * sy * eps := le_of_not_gt hnonneg
        have hprod_nonpos :
            (nwy * sx * eps - nwx * sy * eps) * (nvx * vy * eps - nvy * vx * eps) ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos hnonneg' (le_of_lt hnv_cross_v_neg)
        exact lt_irrefl _ (lt_of_le_of_lt hprod_nonpos hBE_pos)
      exact hnw_cross_s_neg'
  exact hgoal_of_nw_cross_s_nonpos (le_of_lt hnw_cross_s_neg)
