import Mathlib

theorem real_p32 (n : ℕ) (hn : n > 0) (a b c d : Fin n → ℝ) (ha : ∀ i, a i > 0) (hb : ∀ i, b i > 0) (hc : ∀ i, c i > 0) (hd : ∀ i, d i > 0) : (∑ i : Fin n, (a i) * (b i) * (c i) * (d i))^4 ≤ (∑ i : Fin n, (a i)^4) * (∑ i : Fin n, (b i)^4) * (∑ i : Fin n, (c i)^4) * (∑ i : Fin n, (d i)^4) := by
  let S : ℝ := ∑ i : Fin n, (a i) * (b i) * (c i) * (d i)
  let P : ℝ := ∑ i : Fin n, ((a i) * (b i)) ^ 2
  let Q : ℝ := ∑ i : Fin n, ((c i) * (d i)) ^ 2
  let A : ℝ := ∑ i : Fin n, (a i) ^ 4
  let B : ℝ := ∑ i : Fin n, (b i) ^ 4
  let C : ℝ := ∑ i : Fin n, (c i) ^ 4
  let D : ℝ := ∑ i : Fin n, (d i) ^ 4
  have hS_pos : 0 < S := by
    dsimp [S]
    haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    exact Finset.sum_pos
      (fun i _ => mul_pos (mul_pos (mul_pos (ha i) (hb i)) (hc i)) (hd i))
      Finset.univ_nonempty
  have hS_def : S = ∑ i : Fin n, ((a i) * (b i)) * ((c i) * (d i)) := by
    simp [S, mul_assoc]
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hQ_nonneg : 0 ≤ Q := by
    dsimp [Q]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS_sq : S ^ 2 ≤ P * Q := by
    rw [hS_def]
    simpa [P, Q] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
        (fun i : Fin n => (a i) * (b i)) (fun i : Fin n => (c i) * (d i)) :
        (∑ i ∈ (Finset.univ : Finset (Fin n)), ((a i) * (b i)) * ((c i) * (d i))) ^ 2 ≤
          (∑ i ∈ (Finset.univ : Finset (Fin n)), ((a i) * (b i)) ^ 2) *
            ∑ i ∈ (Finset.univ : Finset (Fin n)), ((c i) * (d i)) ^ 2)
  have hP_sq : P ^ 2 ≤ A * B := by
    dsimp [P, A, B]
    convert (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i : Fin n => (a i) ^ 2) (fun i : Fin n => (b i) ^ 2)) using 2 <;> ring_nf
  have hQ_sq : Q ^ 2 ≤ C * D := by
    dsimp [Q, C, D]
    convert (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i : Fin n => (c i) ^ 2) (fun i : Fin n => (d i) ^ 2)) using 2 <;> ring_nf
  have hS_four : S ^ 4 ≤ (P * Q) ^ 2 := by
    calc
      S ^ 4 = (S ^ 2) ^ 2 := by ring_nf
      _ ≤ (P * Q) ^ 2 := by
        exact (sq_le_sq₀ (sq_nonneg S) (mul_nonneg hP_nonneg hQ_nonneg)).2 hS_sq
  have hPQ_sq : (P * Q) ^ 2 ≤ (A * B) * (C * D) := by
    calc
      (P * Q) ^ 2 = P ^ 2 * Q ^ 2 := by ring_nf
      _ ≤ (A * B) * (C * D) := by
        gcongr
  have hmain : S ^ 4 ≤ A * B * C * D := by
    calc
      S ^ 4 ≤ (P * Q) ^ 2 := hS_four
      _ ≤ (A * B) * (C * D) := hPQ_sq
      _ = A * B * C * D := by ring_nf
  simpa [S, A, B, C, D] using hmain
