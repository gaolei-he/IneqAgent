import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


private theorem private_hDS_class_1 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ 3*a^6 + 6*a^5*b + 6*a^5*c + 6*a^5*d + 2*a^4*b^2 + 8*a^4*b*c + 7*a^4*b*d + 3*a^4*c^2 + 8*a^4*c*d + 2*a^4*d^2 - 2*a^3*b^3 - 2*a^3*b^2*c - 3*a^3*b^2*d - 4*a^3*b*c*d - 3*a^3*b*d^2 - 2*a^3*c*d^2 - 2*a^3*d^3 + 2*a^2*b^4 - 3*a^2*b^3*c - 2*a^2*b^3*d - 8*a^2*b^2*c^2 - 19*a^2*b^2*c*d - 8*a^2*b^2*d^2 - 16*a^2*b*c^2*d - 19*a^2*b*c*d^2 - 2*a^2*b*d^3 + 3*a^2*c^4 - 8*a^2*c^2*d^2 - 3*a^2*c*d^3 + 2*a^2*d^4 + 6*a*b^5 + 7*a*b^4*c + 8*a*b^4*d - 3*a*b^3*c^2 - 4*a*b^3*c*d - 2*a*b^2*c^3 - 19*a*b^2*c^2*d - 16*a*b^2*c*d^2 + 8*a*b*c^4 - 4*a*b*c^3*d - 19*a*b*c^2*d^2 - 4*a*b*c*d^3 + 8*a*b*d^4 + 6*a*c^5 + 8*a*c^4*d - 2*a*c^3*d^2 - 3*a*c^2*d^3 + 7*a*c*d^4 + 6*a*d^5 + 3*b^6 + 6*b^5*c + 6*b^5*d + 2*b^4*c^2 + 8*b^4*c*d + 3*b^4*d^2 - 2*b^3*c^3 - 2*b^3*c^2*d + 2*b^2*c^4 - 3*b^2*c^3*d - 8*b^2*c^2*d^2 + 3*b^2*d^4 + 6*b*c^5 + 7*b*c^4*d - 3*b*c^3*d^2 - 2*b*c^2*d^3 + 8*b*c*d^4 + 6*b*d^5 + 3*c^6 + 6*c^5*d + 2*c^4*d^2 - 2*c^3*d^3 + 2*c^2*d^4 + 6*c*d^5 + 3*d^6 := by
  intro a b c d h_a_nonneg_base h_b_nonneg_base h_c_nonneg_base h_d_nonneg_base hsort
  have h_a_b : a ≤ b := hsort.1
  have h_b_c : b ≤ c := hsort.2.1
  have h_c_d : c ≤ d := hsort.2.2
  set t1_1 := a
  set t1_2 := b - a
  set t1_3 := c - b
  set t1_4 := d - c
  have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
  have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
  have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
  have h_t1_4_nonneg : t1_4 ≥ 0 := by linarith
  have h_b_eq : b = t1_1 + t1_2 := by
    dsimp [t1_1, t1_2]
    ring_nf
  have h_c_eq : c = t1_1 + t1_2 + t1_3 := by
    dsimp [t1_1, t1_2, t1_3]
    ring_nf
  have h_d_eq : d = t1_1 + t1_2 + t1_3 + t1_4 := by
    dsimp [t1_1, t1_2, t1_3, t1_4]
    ring_nf
  rw [h_b_eq, h_c_eq, h_d_eq]
  suffices hleaf : (0 : ℝ) ≤ 270*t1_1^4*t1_2^2 + 333*t1_1^4*t1_2*t1_3 + 207*t1_1^4*t1_2*t1_4 + 333*t1_1^4*t1_3^2 + 333*t1_1^4*t1_3*t1_4 + 270*t1_1^4*t1_4^2 + 738*t1_1^3*t1_2^3 + 1395*t1_1^3*t1_2^2*t1_3 + 819*t1_1^3*t1_2^2*t1_4 + 1665*t1_1^3*t1_2*t1_3^2 + 1746*t1_1^3*t1_2*t1_3*t1_4 + 1089*t1_1^3*t1_2*t1_4^2 + 666*t1_1^3*t1_3^3 + 999*t1_1^3*t1_3^2*t1_4 + 1017*t1_1^3*t1_3*t1_4^2 + 342*t1_1^3*t1_4^3 + 759*t1_1^2*t1_2^4 + 1934*t1_1^2*t1_2^3*t1_3 + 1102*t1_1^2*t1_2^3*t1_4 + 2836*t1_1^2*t1_2^2*t1_3^2 + 3016*t1_1^2*t1_2^2*t1_3*t1_4 + 1588*t1_1^2*t1_2^2*t1_4^2 + 1993*t1_1^2*t1_2*t1_3^3 + 3048*t1_1^2*t1_2*t1_3^2*t1_4 + 2854*t1_1^2*t1_2*t1_3*t1_4^2 + 913*t1_1^2*t1_2*t1_4^3 + 497*t1_1^2*t1_3^4 + 994*t1_1^2*t1_3^3*t1_4 + 1270*t1_1^2*t1_3^2*t1_4^2 + 773*t1_1^2*t1_3*t1_4^3 + 165*t1_1^2*t1_4^4 + 348*t1_1*t1_2^5 + 1116*t1_1*t1_2^4*t1_3 + 624*t1_1*t1_2^4*t1_4 + 1976*t1_1*t1_2^3*t1_3^2 + 2108*t1_1*t1_2^3*t1_3*t1_4 + 992*t1_1*t1_2^3*t1_4^2 + 1915*t1_1*t1_2^2*t1_3^3 + 2958*t1_1*t1_2^2*t1_3^2*t1_4 + 2598*t1_1*t1_2^2*t1_3*t1_4^2 + 797*t1_1*t1_2^2*t1_4^3 + 907*t1_1*t1_2*t1_3^4 + 1832*t1_1*t1_2*t1_3^3*t1_4 + 2260*t1_1*t1_2*t1_3^2*t1_4^2 + 1338*t1_1*t1_2*t1_3*t1_4^3 + 281*t1_1*t1_2*t1_4^4 + 164*t1_1*t1_3^5 + 410*t1_1*t1_3^4*t1_4 + 642*t1_1*t1_3^3*t1_4^2 + 553*t1_1*t1_3^2*t1_4^3 + 229*t1_1*t1_3*t1_4^4 + 36*t1_1*t1_4^5 + 60*t1_2^6 + 232*t1_2^5*t1_3 + 128*t1_2^5*t1_4 + 485*t1_2^4*t1_3^2 + 517*t1_2^4*t1_3*t1_4 + 225*t1_2^4*t1_4^2 + 592*t1_2^3*t1_3^3 + 919*t1_2^3*t1_3^2*t1_4 + 769*t1_2^3*t1_3*t1_4^2 + 228*t1_2^3*t1_4^3 + 404*t1_2^2*t1_3^4 + 821*t1_2^2*t1_3^3*t1_4 + 985*t1_2^2*t1_3^2*t1_4^2 + 570*t1_2^2*t1_3*t1_4^3 + 118*t1_2^2*t1_4^4 + 142*t1_2*t1_3^5 + 357*t1_2*t1_3^4*t1_4 + 551*t1_2*t1_3^3*t1_4^2 + 468*t1_2*t1_3^2*t1_4^3 + 192*t1_2*t1_3*t1_4^4 + 30*t1_2*t1_4^5 + 20*t1_3^6 + 60*t1_3^5*t1_4 + 113*t1_3^4*t1_4^2 + 126*t1_3^3*t1_4^3 + 77*t1_3^2*t1_4^4 + 24*t1_3*t1_4^5 + 3*t1_4^6 by
    convert hleaf using 1 <;> ring
  positivity

private theorem private_hDS_class_2 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ 3*a^6 + 6*a^5*b + 6*a^5*c + 6*a^5*d + 2*a^4*b^2 + 7*a^4*b*c + 8*a^4*b*d + 2*a^4*c^2 + 8*a^4*c*d + 3*a^4*d^2 - 2*a^3*b^3 - 3*a^3*b^2*c - 2*a^3*b^2*d - 3*a^3*b*c^2 - 4*a^3*b*c*d - 2*a^3*c^3 - 2*a^3*c^2*d + 2*a^2*b^4 - 2*a^2*b^3*c - 3*a^2*b^3*d - 8*a^2*b^2*c^2 - 19*a^2*b^2*c*d - 8*a^2*b^2*d^2 - 2*a^2*b*c^3 - 19*a^2*b*c^2*d - 16*a^2*b*c*d^2 + 2*a^2*c^4 - 3*a^2*c^3*d - 8*a^2*c^2*d^2 + 3*a^2*d^4 + 6*a*b^5 + 8*a*b^4*c + 7*a*b^4*d - 4*a*b^3*c*d - 3*a*b^3*d^2 - 16*a*b^2*c^2*d - 19*a*b^2*c*d^2 - 2*a*b^2*d^3 + 8*a*b*c^4 - 4*a*b*c^3*d - 19*a*b*c^2*d^2 - 4*a*b*c*d^3 + 8*a*b*d^4 + 6*a*c^5 + 7*a*c^4*d - 3*a*c^3*d^2 - 2*a*c^2*d^3 + 8*a*c*d^4 + 6*a*d^5 + 3*b^6 + 6*b^5*c + 6*b^5*d + 3*b^4*c^2 + 8*b^4*c*d + 2*b^4*d^2 - 2*b^3*c*d^2 - 2*b^3*d^3 + 3*b^2*c^4 - 8*b^2*c^2*d^2 - 3*b^2*c*d^3 + 2*b^2*d^4 + 6*b*c^5 + 8*b*c^4*d - 2*b*c^3*d^2 - 3*b*c^2*d^3 + 7*b*c*d^4 + 6*b*d^5 + 3*c^6 + 6*c^5*d + 2*c^4*d^2 - 2*c^3*d^3 + 2*c^2*d^4 + 6*c*d^5 + 3*d^6 := by
  intro a b c d h_a_nonneg_base h_b_nonneg_base h_c_nonneg_base h_d_nonneg_base hsort
  have h_a_b : a ≤ b := hsort.1
  have h_b_c : b ≤ c := hsort.2.1
  have h_c_d : c ≤ d := hsort.2.2
  set t1_1 := a
  set t1_2 := b - a
  set t1_3 := c - b
  set t1_4 := d - c
  have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
  have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
  have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
  have h_t1_4_nonneg : t1_4 ≥ 0 := by linarith
  have h_b_eq : b = t1_1 + t1_2 := by
    dsimp [t1_1, t1_2]
    ring_nf
  have h_c_eq : c = t1_1 + t1_2 + t1_3 := by
    dsimp [t1_1, t1_2, t1_3]
    ring_nf
  have h_d_eq : d = t1_1 + t1_2 + t1_3 + t1_4 := by
    dsimp [t1_1, t1_2, t1_3, t1_4]
    ring_nf
  rw [h_b_eq, h_c_eq, h_d_eq]
  suffices hleaf : (0 : ℝ) ≤ 270*t1_1^4*t1_2^2 + 333*t1_1^4*t1_2*t1_3 + 126*t1_1^4*t1_2*t1_4 + 333*t1_1^4*t1_3^2 + 333*t1_1^4*t1_3*t1_4 + 270*t1_1^4*t1_4^2 + 738*t1_1^3*t1_2^3 + 1395*t1_1^3*t1_2^2*t1_3 + 576*t1_1^3*t1_2^2*t1_4 + 1665*t1_1^3*t1_2*t1_3^2 + 1584*t1_1^3*t1_2*t1_3*t1_4 + 1008*t1_1^3*t1_2*t1_4^2 + 666*t1_1^3*t1_3^3 + 999*t1_1^3*t1_3^2*t1_4 + 1017*t1_1^3*t1_3*t1_4^2 + 342*t1_1^3*t1_4^3 + 759*t1_1^2*t1_2^4 + 1934*t1_1^2*t1_2^3*t1_3 + 832*t1_1^2*t1_2^3*t1_4 + 2836*t1_1^2*t1_2^2*t1_3^2 + 2656*t1_1^2*t1_2^2*t1_3*t1_4 + 1408*t1_1^2*t1_2^2*t1_4^2 + 1993*t1_1^2*t1_2*t1_3^3 + 2931*t1_1^2*t1_2*t1_3^2*t1_4 + 2737*t1_1^2*t1_2*t1_3*t1_4^2 + 886*t1_1^2*t1_2*t1_4^3 + 497*t1_1^2*t1_3^4 + 994*t1_1^2*t1_3^3*t1_4 + 1270*t1_1^2*t1_3^2*t1_4^2 + 773*t1_1^2*t1_3*t1_4^3 + 165*t1_1^2*t1_4^4 + 348*t1_1*t1_2^5 + 1116*t1_1*t1_2^4*t1_3 + 492*t1_1*t1_2^4*t1_4 + 1976*t1_1*t1_2^3*t1_3^2 + 1844*t1_1*t1_2^3*t1_3*t1_4 + 860*t1_1*t1_2^3*t1_4^2 + 1915*t1_1*t1_2^2*t1_3^3 + 2787*t1_1*t1_2^2*t1_3^2*t1_4 + 2427*t1_1*t1_2^2*t1_3*t1_4^2 + 758*t1_1*t1_2^2*t1_4^3 + 907*t1_1*t1_2*t1_3^4 + 1796*t1_1*t1_2*t1_3^3*t1_4 + 2206*t1_1*t1_2*t1_3^2*t1_4^2 + 1314*t1_1*t1_2*t1_3*t1_4^3 + 278*t1_1*t1_2*t1_4^4 + 164*t1_1*t1_3^5 + 410*t1_1*t1_3^4*t1_4 + 642*t1_1*t1_3^3*t1_4^2 + 553*t1_1*t1_3^2*t1_4^3 + 229*t1_1*t1_3*t1_4^4 + 36*t1_1*t1_4^5 + 60*t1_2^6 + 232*t1_2^5*t1_3 + 104*t1_2^5*t1_4 + 485*t1_2^4*t1_3^2 + 453*t1_2^4*t1_3*t1_4 + 193*t1_2^4*t1_4^2 + 592*t1_2^3*t1_3^3 + 857*t1_2^3*t1_3^2*t1_4 + 707*t1_2^3*t1_3*t1_4^2 + 214*t1_2^3*t1_4^3 + 404*t1_2^2*t1_3^4 + 795*t1_2^2*t1_3^3*t1_4 + 946*t1_2^2*t1_3^2*t1_4^2 + 553*t1_2^2*t1_3*t1_4^3 + 116*t1_2^2*t1_4^4 + 142*t1_2*t1_3^5 + 353*t1_2*t1_3^4*t1_4 + 543*t1_2*t1_3^3*t1_4^2 + 463*t1_2*t1_3^2*t1_4^3 + 191*t1_2*t1_3*t1_4^4 + 30*t1_2*t1_4^5 + 20*t1_3^6 + 60*t1_3^5*t1_4 + 113*t1_3^4*t1_4^2 + 126*t1_3^3*t1_4^3 + 77*t1_3^2*t1_4^4 + 24*t1_3*t1_4^5 + 3*t1_4^6 by
    convert hleaf using 1 <;> ring
  positivity

private theorem private_hDS_class_3 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ 3*a^6 + 6*a^5*b + 6*a^5*c + 6*a^5*d + 3*a^4*b^2 + 8*a^4*b*c + 8*a^4*b*d + 2*a^4*c^2 + 7*a^4*c*d + 2*a^4*d^2 - 2*a^3*b*c^2 - 4*a^3*b*c*d - 2*a^3*b*d^2 - 2*a^3*c^3 - 3*a^3*c^2*d - 3*a^3*c*d^2 - 2*a^3*d^3 + 3*a^2*b^4 - 8*a^2*b^2*c^2 - 16*a^2*b^2*c*d - 8*a^2*b^2*d^2 - 3*a^2*b*c^3 - 19*a^2*b*c^2*d - 19*a^2*b*c*d^2 - 3*a^2*b*d^3 + 2*a^2*c^4 - 2*a^2*c^3*d - 8*a^2*c^2*d^2 - 2*a^2*c*d^3 + 2*a^2*d^4 + 6*a*b^5 + 8*a*b^4*c + 8*a*b^4*d - 2*a*b^3*c^2 - 4*a*b^3*c*d - 2*a*b^3*d^2 - 3*a*b^2*c^3 - 19*a*b^2*c^2*d - 19*a*b^2*c*d^2 - 3*a*b^2*d^3 + 7*a*b*c^4 - 4*a*b*c^3*d - 16*a*b*c^2*d^2 - 4*a*b*c*d^3 + 7*a*b*d^4 + 6*a*c^5 + 8*a*c^4*d + 8*a*c*d^4 + 6*a*d^5 + 3*b^6 + 6*b^5*c + 6*b^5*d + 2*b^4*c^2 + 7*b^4*c*d + 2*b^4*d^2 - 2*b^3*c^3 - 3*b^3*c^2*d - 3*b^3*c*d^2 - 2*b^3*d^3 + 2*b^2*c^4 - 2*b^2*c^3*d - 8*b^2*c^2*d^2 - 2*b^2*c*d^3 + 2*b^2*d^4 + 6*b*c^5 + 8*b*c^4*d + 8*b*c*d^4 + 6*b*d^5 + 3*c^6 + 6*c^5*d + 3*c^4*d^2 + 3*c^2*d^4 + 6*c*d^5 + 3*d^6 := by
  intro a b c d h_a_nonneg_base h_b_nonneg_base h_c_nonneg_base h_d_nonneg_base hsort
  have h_a_b : a ≤ b := hsort.1
  have h_b_c : b ≤ c := hsort.2.1
  have h_c_d : c ≤ d := hsort.2.2
  set t1_1 := a
  set t1_2 := b - a
  set t1_3 := c - b
  set t1_4 := d - c
  have h_t1_1_nonneg : t1_1 ≥ 0 := by linarith
  have h_t1_2_nonneg : t1_2 ≥ 0 := by linarith
  have h_t1_3_nonneg : t1_3 ≥ 0 := by linarith
  have h_t1_4_nonneg : t1_4 ≥ 0 := by linarith
  have h_b_eq : b = t1_1 + t1_2 := by
    dsimp [t1_1, t1_2]
    ring_nf
  have h_c_eq : c = t1_1 + t1_2 + t1_3 := by
    dsimp [t1_1, t1_2, t1_3]
    ring_nf
  have h_d_eq : d = t1_1 + t1_2 + t1_3 + t1_4 := by
    dsimp [t1_1, t1_2, t1_3, t1_4]
    ring_nf
  rw [h_b_eq, h_c_eq, h_d_eq]
  suffices hleaf : (0 : ℝ) ≤ 270*t1_1^4*t1_2^2 + 414*t1_1^4*t1_2*t1_3 + 207*t1_1^4*t1_2*t1_4 + 414*t1_1^4*t1_3^2 + 414*t1_1^4*t1_3*t1_4 + 270*t1_1^4*t1_4^2 + 738*t1_1^3*t1_2^3 + 1638*t1_1^3*t1_2^2*t1_3 + 819*t1_1^3*t1_2^2*t1_4 + 2070*t1_1^3*t1_2*t1_3^2 + 2070*t1_1^3*t1_2*t1_3*t1_4 + 1089*t1_1^3*t1_2*t1_4^2 + 828*t1_1^3*t1_3^3 + 1242*t1_1^3*t1_3^2*t1_4 + 1098*t1_1^3*t1_3*t1_4^2 + 342*t1_1^3*t1_4^3 + 759*t1_1^2*t1_2^4 + 2204*t1_1^2*t1_2^3*t1_3 + 1102*t1_1^2*t1_2^3*t1_4 + 3466*t1_1^2*t1_2^2*t1_3^2 + 3466*t1_1^2*t1_2^2*t1_3*t1_4 + 1588*t1_1^2*t1_2^2*t1_4^2 + 2470*t1_1^2*t1_2*t1_3^3 + 3705*t1_1^2*t1_2*t1_3^2*t1_4 + 3061*t1_1^2*t1_2*t1_3*t1_4^2 + 913*t1_1^2*t1_2*t1_4^3 + 614*t1_1^2*t1_3^4 + 1228*t1_1^2*t1_3^3*t1_4 + 1414*t1_1^2*t1_3^2*t1_4^2 + 800*t1_1^2*t1_3*t1_4^3 + 165*t1_1^2*t1_4^4 + 348*t1_1*t1_2^5 + 1248*t1_1*t1_2^4*t1_3 + 624*t1_1*t1_2^4*t1_4 + 2372*t1_1*t1_2^3*t1_3^2 + 2372*t1_1*t1_2^3*t1_3*t1_4 + 992*t1_1*t1_2^3*t1_4^2 + 2350*t1_1*t1_2^2*t1_3^3 + 3525*t1_1*t1_2^2*t1_3^2*t1_4 + 2769*t1_1*t1_2^2*t1_3*t1_4^2 + 797*t1_1*t1_2^2*t1_4^3 + 1114*t1_1*t1_2*t1_3^4 + 2228*t1_1*t1_2*t1_3^3*t1_4 + 2494*t1_1*t1_2*t1_3^2*t1_4^2 + 1380*t1_1*t1_2*t1_3*t1_4^3 + 281*t1_1*t1_2*t1_4^4 + 200*t1_1*t1_3^5 + 500*t1_1*t1_3^4*t1_4 + 720*t1_1*t1_3^3*t1_4^2 + 580*t1_1*t1_3^2*t1_4^3 + 232*t1_1*t1_3*t1_4^4 + 36*t1_1*t1_4^5 + 60*t1_2^6 + 256*t1_2^5*t1_3 + 128*t1_2^5*t1_4 + 573*t1_2^4*t1_3^2 + 573*t1_2^4*t1_3*t1_4 + 225*t1_2^4*t1_4^2 + 718*t1_2^3*t1_3^3 + 1077*t1_2^3*t1_3^2*t1_4 + 815*t1_2^3*t1_3*t1_4^2 + 228*t1_2^3*t1_4^3 + 492*t1_2^2*t1_3^4 + 984*t1_2^2*t1_3^3*t1_4 + 1078*t1_2^2*t1_3^2*t1_4^2 + 586*t1_2^2*t1_3*t1_4^3 + 118*t1_2^2*t1_4^4 + 172*t1_2*t1_3^5 + 430*t1_2*t1_3^4*t1_4 + 612*t1_2*t1_3^3*t1_4^2 + 488*t1_2*t1_3^2*t1_4^3 + 194*t1_2*t1_3*t1_4^4 + 30*t1_2*t1_4^5 + 24*t1_3^6 + 72*t1_3^5*t1_4 + 126*t1_3^4*t1_4^2 + 132*t1_3^3*t1_4^3 + 78*t1_3^2*t1_4^4 + 24*t1_3*t1_4^5 + 3*t1_4^6 by
    convert hleaf using 1 <;> ring
  positivity

theorem P1' {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a * b + b * c + c * d + d * a = 1) : 1 / 3 ≤ a ^ 3 / (b + c + d) + b ^ 3 / (c + d + a) + c ^ 3 / (d + a + b) + d ^ 3 / (a + b + c) := by
  rw [← sub_nonneg]
  have hden1_pos : 0 < b + c + d := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd, h]
  have hden1_ne : b + c + d ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < a + c + d := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd, h]
  have hden2_ne : a + c + d ≠ 0 := ne_of_gt hden2_pos
  have hden3_pos : 0 < a + b + d := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd, h]
  have hden3_ne : a + b + d ≠ 0 := ne_of_gt hden3_pos
  have hden4_pos : 0 < a + b + c := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd, h]
  have hden4_ne : a + b + c ≠ 0 := ne_of_gt hden4_pos
  field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm, hd.ne.symm, hden1_pos, hden2_pos, hden3_pos, hden4_pos, hden1_ne, hden2_ne, hden3_ne, hden4_ne]
  ring_nf
  have hQ : a*b + a*d + b*c + c*d = 1 := by nlinarith [h]
  have hQunit : a*b + a*d + b*c + c*d = 1 := by nlinarith [hQ]
  suffices hH :
      0 ≤ 3*a^3*(a + b + c)*(a + b + d)*(a + c + d) + 3*b^3*(a + b + c)*(a + b + d)*(b + c + d) + 3*c^3*(a + b + c)*(a + c + d)*(b + c + d) + 3*d^3*(a + b + d)*(a + c + d)*(b + c + d) - (a + b + c)*(a + b + d)*(a + c + d)*(b + c + d)*(a*b + a*d + b*c + c*d) by
    convert hH using 1
    try rw [hQunit]
    try rw [hQ]
    ring_nf
  ring_nf
  clear h hQ hQunit
  clear hden1_pos hden2_pos hden3_pos hden4_pos hden1_ne hden2_ne hden3_ne hden4_ne
  have hDS_class_1 := private_hDS_class_1
  have hDS_class_2 := private_hDS_class_2
  have hDS_class_3 := private_hDS_class_3
  have h_b_a := le_total b a
  rcases h_b_a with h_b_a | h_a_b
  ·
    have h_c_b := le_total c b
    rcases h_c_b with h_c_b | h_b_c
    ·
      have h_d_c := le_total d c
      rcases h_d_c with h_d_c | h_c_d
      ·
        have hs : d ≤ c ∧ c ≤ b ∧ b ≤ a := by
          constructor
          · linarith
          ·
            constructor
            · linarith
            ·
              linarith
        have hcert := hDS_class_1 d c b a (by positivity) (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring
      ·
        have h_d_b := le_total d b
        rcases h_d_b with h_d_b | h_b_d
        ·
          have hs : c ≤ d ∧ d ≤ b ∧ b ≤ a := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_2 c d b a (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_a := le_total d a
          rcases h_d_a with h_d_a | h_a_d
          ·
            have hs : c ≤ b ∧ b ≤ d ∧ d ≤ a := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_2 c b d a (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have hs : c ≤ b ∧ b ≤ a ∧ a ≤ d := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_1 c b a d (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
    ·
      have h_c_a := le_total c a
      rcases h_c_a with h_c_a | h_a_c
      ·
        have h_d_b := le_total d b
        rcases h_d_b with h_d_b | h_b_d
        ·
          have hs : d ≤ b ∧ b ≤ c ∧ c ≤ a := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_3 d b c a (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_c := le_total d c
          rcases h_d_c with h_d_c | h_c_d
          ·
            have hs : b ≤ d ∧ d ≤ c ∧ c ≤ a := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_3 b d c a (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have h_d_a := le_total d a
            rcases h_d_a with h_d_a | h_a_d
            ·
              have hs : b ≤ c ∧ c ≤ d ∧ d ≤ a := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_1 b c d a (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
            ·
              have hs : b ≤ c ∧ c ≤ a ∧ a ≤ d := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_2 b c a d (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
      ·
        have h_d_b := le_total d b
        rcases h_d_b with h_d_b | h_b_d
        ·
          have hs : d ≤ b ∧ b ≤ a ∧ a ≤ c := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_3 d b a c (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_a := le_total d a
          rcases h_d_a with h_d_a | h_a_d
          ·
            have hs : b ≤ d ∧ d ≤ a ∧ a ≤ c := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_3 b d a c (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have h_d_c := le_total d c
            rcases h_d_c with h_d_c | h_c_d
            ·
              have hs : b ≤ a ∧ a ≤ d ∧ d ≤ c := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_1 b a d c (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
            ·
              have hs : b ≤ a ∧ a ≤ c ∧ c ≤ d := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_2 b a c d (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
  ·
    have h_c_a := le_total c a
    rcases h_c_a with h_c_a | h_a_c
    ·
      have h_d_c := le_total d c
      rcases h_d_c with h_d_c | h_c_d
      ·
        have hs : d ≤ c ∧ c ≤ a ∧ a ≤ b := by
          constructor
          · linarith
          ·
            constructor
            · linarith
            ·
              linarith
        have hcert := hDS_class_2 d c a b (by positivity) (by positivity) (by positivity) (by positivity) hs
        convert hcert using 1 <;> ring
      ·
        have h_d_a := le_total d a
        rcases h_d_a with h_d_a | h_a_d
        ·
          have hs : c ≤ d ∧ d ≤ a ∧ a ≤ b := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_1 c d a b (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_b := le_total d b
          rcases h_d_b with h_d_b | h_b_d
          ·
            have hs : c ≤ a ∧ a ≤ d ∧ d ≤ b := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_3 c a d b (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have hs : c ≤ a ∧ a ≤ b ∧ b ≤ d := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_3 c a b d (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
    ·
      have h_c_b := le_total c b
      rcases h_c_b with h_c_b | h_b_c
      ·
        have h_d_a := le_total d a
        rcases h_d_a with h_d_a | h_a_d
        ·
          have hs : d ≤ a ∧ a ≤ c ∧ c ≤ b := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_2 d a c b (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_c := le_total d c
          rcases h_d_c with h_d_c | h_c_d
          ·
            have hs : a ≤ d ∧ d ≤ c ∧ c ≤ b := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_1 a d c b (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have h_d_b := le_total d b
            rcases h_d_b with h_d_b | h_b_d
            ·
              have hs : a ≤ c ∧ c ≤ d ∧ d ≤ b := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_3 a c d b (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
            ·
              have hs : a ≤ c ∧ c ≤ b ∧ b ≤ d := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_3 a c b d (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
      ·
        have h_d_a := le_total d a
        rcases h_d_a with h_d_a | h_a_d
        ·
          have hs : d ≤ a ∧ a ≤ b ∧ b ≤ c := by
            constructor
            · linarith
            ·
              constructor
              · linarith
              ·
                linarith
          have hcert := hDS_class_1 d a b c (by positivity) (by positivity) (by positivity) (by positivity) hs
          convert hcert using 1 <;> ring
        ·
          have h_d_b := le_total d b
          rcases h_d_b with h_d_b | h_b_d
          ·
            have hs : a ≤ d ∧ d ≤ b ∧ b ≤ c := by
              constructor
              · linarith
              ·
                constructor
                · linarith
                ·
                  linarith
            have hcert := hDS_class_2 a d b c (by positivity) (by positivity) (by positivity) (by positivity) hs
            convert hcert using 1 <;> ring
          ·
            have h_d_c := le_total d c
            rcases h_d_c with h_d_c | h_c_d
            ·
              have hs : a ≤ b ∧ b ≤ d ∧ d ≤ c := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_2 a b d c (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring
            ·
              have hs : a ≤ b ∧ b ≤ c ∧ c ≤ d := by
                constructor
                · linarith
                ·
                  constructor
                  · linarith
                  ·
                    linarith
              have hcert := hDS_class_1 a b c d (by positivity) (by positivity) (by positivity) (by positivity) hs
              convert hcert using 1 <;> ring



theorem P1 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a * b + b * c + c * d + d * a = 1) : 1 / 3 ≤ a ^ 3 / (b + c + d) + b ^ 3 / (c + d + a) + c ^ 3 / (d + a + b) + d ^ 3 / (a + b + c) := by
  exact @P1' a b c d ha hb hc hd h
