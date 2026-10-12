import Mathlib

private lemma fin_sq_sum_le_mul_card {n : ℕ} (f : Fin n → ℝ) :
    (∑ i : Fin n, f i) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, (f i) ^ 2 := by
  simpa using
    (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := f))

private lemma fin_sq_sum_div_le_sum_sq_div {n : ℕ} (f : Fin n → ℝ) {g : Fin n → ℝ}
    (hg : ∀ i, 0 < g i) :
    (∑ i : Fin n, f i) ^ 2 / (∑ i : Fin n, g i) ≤
      ∑ i : Fin n, (f i) ^ 2 / g i := by
  simpa using
    (Finset.sq_sum_div_le_sum_sq_div (s := (Finset.univ : Finset (Fin n))) (f := f) (g := g)
      (by intro i hi; exact hg i))

theorem real_p37 (n : ℕ) (hn : n ≥ 2) (x : Fin n → ℝ) (hx : ∀ i, x i > 0) (h : ∑ i : Fin n, x i = 1) : ∑ i : Fin n, (x i / √(1 - x i)) ≥ 1 / √(n - 1) * ∑ i : Fin n, √(x i) := by
  have hx_lt_one : ∀ i, x i < 1 := by
    intro i
    classical
    have hsplit : (∑ j ∈ Finset.univ.erase i, x j) + x i = 1 := by
      simp [h]
    have htail_pos : 0 < ∑ j ∈ Finset.univ.erase i, x j := by
      obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (a := i) (by simpa using hn)
      refine Finset.sum_pos (fun j _ => hx j) ⟨j, ?_⟩
      exact Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    nlinarith
  let a : Fin n → ℝ := fun i => Real.sqrt (1 - x i)
  have ha_sq : ∀ i, (a i) ^ 2 = 1 - x i := by
    intro i
    have hsq : (Real.sqrt (1 - x i)) ^ 2 = 1 - x i :=
      Real.sq_sqrt (sub_nonneg.mpr (le_of_lt (hx_lt_one i)))
    simpa [a] using hsq
  have ha_pos : ∀ i, 0 < a i := by
    intro i
    have hpos : 0 < Real.sqrt (1 - x i) :=
      Real.sqrt_pos.mpr (sub_pos.mpr (hx_lt_one i))
    simpa [a] using hpos
  have hsum_a_sq : ∑ i : Fin n, (a i) ^ 2 = (n : ℝ) - 1 := by
    calc
      ∑ i : Fin n, (a i) ^ 2 = ∑ i : Fin n, (1 - x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ha_sq i]
      _ = (∑ _ : Fin n, (1 : ℝ)) - ∑ i : Fin n, x i := by
        rw [Finset.sum_sub_distrib]
      _ = (n : ℝ) - 1 := by
        simp [h]
  have hA_sq_le : (∑ i : Fin n, a i) ^ 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
    have hCauchy := fin_sq_sum_le_mul_card a
    calc
      (∑ i : Fin n, a i) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, (a i) ^ 2 := hCauchy
      _ = (n : ℝ) * ((n : ℝ) - 1) := by rw [hsum_a_sq]
  have hA_pos : 0 < ∑ i : Fin n, a i := by
    let j0 : Fin n := ⟨0, by omega⟩
    exact Finset.sum_pos (fun i _ => ha_pos i) ⟨j0, Finset.mem_univ j0⟩
  have hB_ge : (n : ℝ) ^ 2 / (∑ i : Fin n, a i) ≤ ∑ i : Fin n, (a i)⁻¹ := by
    have hTitu :=
      fin_sq_sum_div_le_sum_sq_div (f := fun _ : Fin n => (1 : ℝ)) (g := a) ha_pos
    simpa using hTitu
  have hLHS_eq :
      (∑ i : Fin n, x i / √(1 - x i)) =
        (∑ i : Fin n, (a i)⁻¹) - ∑ i : Fin n, a i := by
    calc
      (∑ i : Fin n, x i / √(1 - x i)) = ∑ i : Fin n, ((a i)⁻¹ - a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hxeq : x i = 1 - (a i) ^ 2 := by
          nlinarith [ha_sq i]
        have hsqrt : Real.sqrt (1 - x i) = a i := by rfl
        calc
          x i / Real.sqrt (1 - x i) = x i / a i := by rw [hsqrt]
          _ = (1 - (a i) ^ 2) / a i := by rw [hxeq]
          _ = (a i)⁻¹ - a i := by
            field_simp [ha_pos i]
      _ = (∑ i : Fin n, (a i)⁻¹) - ∑ i : Fin n, a i := by
        rw [Finset.sum_sub_distrib]
  have hsum_sqrt_sq : ∑ i : Fin n, (Real.sqrt (x i)) ^ 2 = 1 := by
    calc
      ∑ i : Fin n, (Real.sqrt (x i)) ^ 2 = ∑ i : Fin n, x i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.sq_sqrt (le_of_lt (hx i))]
      _ = 1 := h
  have hS_sq_le : (∑ i : Fin n, Real.sqrt (x i)) ^ 2 ≤ (n : ℝ) := by
    have hCauchy := fin_sq_sum_le_mul_card (fun i : Fin n => Real.sqrt (x i))
    calc
      (∑ i : Fin n, Real.sqrt (x i)) ^ 2 ≤
          (n : ℝ) * ∑ i : Fin n, (Real.sqrt (x i)) ^ 2 := hCauchy
      _ = (n : ℝ) := by rw [hsum_sqrt_sq, mul_one]
  have hS_nonneg : 0 ≤ ∑ i : Fin n, Real.sqrt (x i) := by
    exact Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hS_le_sqrt_n : ∑ i : Fin n, Real.sqrt (x i) ≤ Real.sqrt (n : ℝ) := by
    have hsq : (∑ i : Fin n, Real.sqrt (x i)) ^ 2 ≤ (Real.sqrt (n : ℝ)) ^ 2 := by
      rwa [Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ))]
    exact (sq_le_sq₀ hS_nonneg (Real.sqrt_nonneg _)).mp hsq
  have hnR : 0 < (n : ℝ) - 1 := by
    have hcast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  let c : ℝ := Real.sqrt ((n : ℝ) / ((n : ℝ) - 1))
  have hc_sq : c ^ 2 = (n : ℝ) / ((n : ℝ) - 1) := by
    dsimp [c]
    exact Real.sq_sqrt (div_nonneg (by positivity) (le_of_lt hnR))
  have hcA_sq_le :
      (c * (∑ i : Fin n, a i)) ^ 2 ≤ (n : ℝ) ^ 2 := by
    have hfac : 0 ≤ (n : ℝ) / ((n : ℝ) - 1) := by positivity
    calc
      (c * (∑ i : Fin n, a i)) ^ 2 =
          c ^ 2 * ((∑ i : Fin n, a i) ^ 2) := by ring
      _ = ((n : ℝ) / ((n : ℝ) - 1)) * ((∑ i : Fin n, a i) ^ 2) := by
        rw [hc_sq]
      _ ≤ ((n : ℝ) / ((n : ℝ) - 1)) * ((n : ℝ) * ((n : ℝ) - 1)) := by
        exact mul_le_mul_of_nonneg_left hA_sq_le hfac
      _ = (n : ℝ) ^ 2 := by
        field_simp [ne_of_gt hnR]
  have hcA_le : c * (∑ i : Fin n, a i) ≤ (n : ℝ) := by
    exact (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hA_pos)) (by positivity)).mp
      hcA_sq_le
  have hAsum_bound :
      ((∑ i : Fin n, a i) ^ 2) + c * (∑ i : Fin n, a i) ≤ (n : ℝ) ^ 2 := by
    nlinarith [hA_sq_le, hcA_le]
  have hLower : c ≤ (n : ℝ) ^ 2 / (∑ i : Fin n, a i) - (∑ i : Fin n, a i) := by
    have hAdd : (∑ i : Fin n, a i) + c ≤ (n : ℝ) ^ 2 / (∑ i : Fin n, a i) := by
      rw [le_div_iff₀ hA_pos]
      nlinarith [hAsum_bound]
    nlinarith
  have hBsubA_ge_c :
      c ≤ (∑ i : Fin n, (a i)⁻¹) - (∑ i : Fin n, a i) := by
    nlinarith [hB_ge, hLower]
  have hRHS_le_c :
      (1 / Real.sqrt ((n : ℝ) - 1)) * (∑ i : Fin n, Real.sqrt (x i)) ≤ c := by
    have hfac : 0 ≤ 1 / Real.sqrt ((n : ℝ) - 1) := by positivity
    calc
      (1 / Real.sqrt ((n : ℝ) - 1)) * (∑ i : Fin n, Real.sqrt (x i)) ≤
          (1 / Real.sqrt ((n : ℝ) - 1)) * Real.sqrt (n : ℝ) := by
        exact mul_le_mul_of_nonneg_left hS_le_sqrt_n hfac
      _ = Real.sqrt ((n : ℝ) / ((n : ℝ) - 1)) := by
        calc
          (1 / Real.sqrt ((n : ℝ) - 1)) * Real.sqrt (n : ℝ) =
              Real.sqrt (n : ℝ) / Real.sqrt ((n : ℝ) - 1) := by ring
          _ = Real.sqrt ((n : ℝ) / ((n : ℝ) - 1)) := by
            rw [← Real.sqrt_div (by positivity : 0 ≤ (n : ℝ)) ((n : ℝ) - 1)]
      _ = c := by rfl
  rw [hLHS_eq]
  exact le_trans hRHS_le_c hBsubA_ge_c
