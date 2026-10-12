import Mathlib

private lemma cube_le (b : ℝ) (hb : 0 ≤ b) : b ^ 3 / (b ^ 3 + 4) ≤ b / 3 := by
  have hb3 : 0 ≤ b ^ 3 := by
    nlinarith [mul_nonneg hb (sq_nonneg b)]
  have hpos : 0 < b ^ 3 + 4 := by nlinarith
  have hpos3 : (0 : ℝ) < 3 := by norm_num
  have hmul : 3 * b ^ 3 ≤ b * (b ^ 3 + 4) := by
    have hfact : 0 ≤ b * (b - 2) ^ 2 * (b + 1) := by
      positivity
    nlinarith
  have hmul' : b ^ 3 ≤ b * (b ^ 3 + 4) / 3 := by
    exact (le_div_iff₀ hpos3).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hmul'' : b ^ 3 ≤ (b / 3) * (b ^ 3 + 4) := by
    convert hmul' using 1
    ring
  exact (div_le_iff₀ hpos).2 hmul''

private lemma edge_ineq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (3 * a - a * b) / 12 ≤ a / (b ^ 3 + 4) := by
  have hpos : 0 < b ^ 3 + 4 := by
    have hb3 : 0 ≤ b ^ 3 := by
      nlinarith [mul_nonneg hb (sq_nonneg b)]
    nlinarith
  have hle : (a / 4) * (b ^ 3 / (b ^ 3 + 4)) ≤ (a / 4) * (b / 3) := by
    exact mul_le_mul_of_nonneg_left (cube_le b hb) (by positivity)
  have h1 : (3 * a - a * b) / 12 = a / 4 - (a / 4) * (b / 3) := by ring
  have h2 : a / 4 - (a / 4) * (b ^ 3 / (b ^ 3 + 4)) = a / (b ^ 3 + 4) := by
    field_simp [hpos.ne']
    ring
  calc
    (3 * a - a * b) / 12 = a / 4 - (a / 4) * (b / 3) := h1
    _ ≤ a / 4 - (a / 4) * (b ^ 3 / (b ^ 3 + 4)) := by linarith
    _ = a / (b ^ 3 + 4) := h2

theorem P19 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (h : a + b + c + d = 4) : a / (b^3 + 4) + b / (c^3 + 4) + c / (d^3 + 4) + d / (a^3 + 4) ≥ 2 / 3 := by
  let S : ℝ := a / (b ^ 3 + 4) + b / (c ^ 3 + 4) + c / (d ^ 3 + 4) + d / (a ^ 3 + 4)
  let T : ℝ := (3 * a - a * b + (3 * b - b * c) + (3 * c - c * d) + (3 * d - d * a)) / 12
  have hT_le_S : T ≤ S := by
    unfold S T
    linarith [edge_ineq a b ha hb, edge_ineq b c hb hc, edge_ineq c d hc hd,
      edge_ineq d a hd ha]
  have hT : T = 1 - (a * b + b * c + c * d + d * a) / 12 := by
    unfold T
    ring_nf
    nlinarith
  have hA : a * b + b * c + c * d + d * a ≤ 4 := by
    have hx : a + c + (b + d) = 4 := by linarith
    have hxy : (a + c) * (b + d) ≤ 4 := by
      have hsq : 0 ≤ (a + c - 2) ^ 2 := sq_nonneg (a + c - 2)
      nlinarith
    calc
      a * b + b * c + c * d + d * a = (a + c) * (b + d) := by ring
      _ ≤ 4 := hxy
  have h2 : 2 / 3 ≤ 1 - (a * b + b * c + c * d + d * a) / 12 := by
    nlinarith
  have h3 : 2 / 3 ≤ T := by
    rw [hT]
    exact h2
  exact le_trans h3 hT_le_S
