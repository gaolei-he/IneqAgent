import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false


private theorem private_hDS_class_1 : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → a ≤ b ∧ b ≤ c ∧ c ≤ d → 0 ≤ a^6*b^2*c^2/256 + a^6*b^2*d^2/256 + a^6*c^2*d^2/256 + a^5*b^3*c^2/64 + a^5*b^3*d^2/64 + a^5*b^2*c^3/64 + a^5*b^2*c^2*d/64 + a^5*b^2*c*d^2/64 + a^5*b^2*d^3/64 + a^5*b*c^2*d^2/64 + a^5*c^3*d^2/64 + a^5*c^2*d^3/64 + 3*a^4*b^4*c^2/128 + 3*a^4*b^4*d^2/128 + 3*a^4*b^3*c^3/64 + 3*a^4*b^3*c^2*d/64 + 3*a^4*b^3*c*d^2/64 + 3*a^4*b^3*d^3/64 + 3*a^4*b^2*c^4/128 + 3*a^4*b^2*c^3*d/64 - 237*a^4*b^2*c^2*d^2/256 + 3*a^4*b^2*c*d^3/64 + 3*a^4*b^2*d^4/128 + 3*a^4*b*c^3*d^2/64 + 3*a^4*b*c^2*d^3/64 + 3*a^4*c^4*d^2/128 + 3*a^4*c^3*d^3/64 + 3*a^4*c^2*d^4/128 + a^3*b^5*c^2/64 + a^3*b^5*d^2/64 + 3*a^3*b^4*c^3/64 + 3*a^3*b^4*c^2*d/64 + 3*a^3*b^4*c*d^2/64 + 3*a^3*b^4*d^3/64 + 3*a^3*b^3*c^4/64 + 3*a^3*b^3*c^3*d/32 + a^3*b^3*c^2*d^2/8 + 3*a^3*b^3*c*d^3/32 + 3*a^3*b^3*d^4/64 + a^3*b^2*c^5/64 + 3*a^3*b^2*c^4*d/64 + a^3*b^2*c^3*d^2/8 + a^3*b^2*c^2*d^3/8 + 3*a^3*b^2*c*d^4/64 + a^3*b^2*d^5/64 + 3*a^3*b*c^4*d^2/64 + 3*a^3*b*c^3*d^3/32 + 3*a^3*b*c^2*d^4/64 + a^3*c^5*d^2/64 + 3*a^3*c^4*d^3/64 + 3*a^3*c^3*d^4/64 + a^3*c^2*d^5/64 + a^2*b^6*c^2/256 + a^2*b^6*d^2/256 + a^2*b^5*c^3/64 + a^2*b^5*c^2*d/64 + a^2*b^5*c*d^2/64 + a^2*b^5*d^3/64 + 3*a^2*b^4*c^4/128 + 3*a^2*b^4*c^3*d/64 - 237*a^2*b^4*c^2*d^2/256 + 3*a^2*b^4*c*d^3/64 + 3*a^2*b^4*d^4/128 + a^2*b^3*c^5/64 + 3*a^2*b^3*c^4*d/64 + a^2*b^3*c^3*d^2/8 + a^2*b^3*c^2*d^3/8 + 3*a^2*b^3*c*d^4/64 + a^2*b^3*d^5/64 + a^2*b^2*c^6/256 + a^2*b^2*c^5*d/64 - 237*a^2*b^2*c^4*d^2/256 + a^2*b^2*c^3*d^3/8 - 237*a^2*b^2*c^2*d^4/256 + a^2*b^2*c*d^5/64 + a^2*b^2*d^6/256 + a^2*b*c^5*d^2/64 + 3*a^2*b*c^4*d^3/64 + 3*a^2*b*c^3*d^4/64 + a^2*b*c^2*d^5/64 + a^2*c^6*d^2/256 + a^2*c^5*d^3/64 + 3*a^2*c^4*d^4/128 + a^2*c^3*d^5/64 + a^2*c^2*d^6/256 + a*b^5*c^2*d^2/64 + 3*a*b^4*c^3*d^2/64 + 3*a*b^4*c^2*d^3/64 + 3*a*b^3*c^4*d^2/64 + 3*a*b^3*c^3*d^3/32 + 3*a*b^3*c^2*d^4/64 + a*b^2*c^5*d^2/64 + 3*a*b^2*c^4*d^3/64 + 3*a*b^2*c^3*d^4/64 + a*b^2*c^2*d^5/64 + b^6*c^2*d^2/256 + b^5*c^3*d^2/64 + b^5*c^2*d^3/64 + 3*b^4*c^4*d^2/128 + 3*b^4*c^3*d^3/64 + 3*b^4*c^2*d^4/128 + b^3*c^5*d^2/64 + 3*b^3*c^4*d^3/64 + 3*b^3*c^3*d^4/64 + b^3*c^2*d^5/64 + b^2*c^6*d^2/256 + b^2*c^5*d^3/64 + 3*b^2*c^4*d^4/128 + b^2*c^3*d^5/64 + b^2*c^2*d^6/256 := by
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
  suffices hleaf : (0 : ℝ) ≤ 3*t1_1^8*t1_2^2/2 + 2*t1_1^8*t1_2*t1_3 + t1_1^8*t1_2*t1_4 + 2*t1_1^8*t1_3^2 + 2*t1_1^8*t1_3*t1_4 + 3*t1_1^8*t1_4^2/2 + 21*t1_1^7*t1_2^3/2 + 21*t1_1^7*t1_2^2*t1_3 + 21*t1_1^7*t1_2^2*t1_4/2 + 20*t1_1^7*t1_2*t1_3^2 + 20*t1_1^7*t1_2*t1_3*t1_4 + 19*t1_1^7*t1_2*t1_4^2/2 + 8*t1_1^7*t1_3^3 + 12*t1_1^7*t1_3^2*t1_4 + 7*t1_1^7*t1_3*t1_4^2 + 3*t1_1^7*t1_4^3/2 + 2049*t1_1^6*t1_2^4/64 + 683*t1_1^6*t1_2^3*t1_3/8 + 683*t1_1^6*t1_2^3*t1_4/16 + 761*t1_1^6*t1_2^2*t1_3^2/8 + 761*t1_1^6*t1_2^2*t1_3*t1_4/8 + 995*t1_1^6*t1_2^2*t1_4^2/32 + 109*t1_1^6*t1_2*t1_3^3/2 + 327*t1_1^6*t1_2*t1_3^2*t1_4/4 + 341*t1_1^6*t1_2*t1_3*t1_4^2/8 + 123*t1_1^6*t1_2*t1_4^3/16 + 53*t1_1^6*t1_3^4/4 + 53*t1_1^6*t1_3^3*t1_4/2 + 145*t1_1^6*t1_3^2*t1_4^2/8 + 39*t1_1^6*t1_3*t1_4^3/8 + 33*t1_1^6*t1_4^4/64 + 7089*t1_1^5*t1_2^5/128 + 11815*t1_1^5*t1_2^4*t1_3/64 + 11815*t1_1^5*t1_2^4*t1_4/128 + 4011*t1_1^5*t1_2^3*t1_3^2/16 + 4011*t1_1^5*t1_2^3*t1_3*t1_4/16 + 4229*t1_1^5*t1_2^3*t1_4^2/64 + 1429*t1_1^5*t1_2^2*t1_3^3/8 + 4287*t1_1^5*t1_2^2*t1_3^2*t1_4/16 + 4113*t1_1^5*t1_2^2*t1_3*t1_4^2/32 + 1255*t1_1^5*t1_2^2*t1_4^3/64 + 553*t1_1^5*t1_2*t1_3^4/8 + 553*t1_1^5*t1_2*t1_3^3*t1_4/4 + 1497*t1_1^5*t1_2*t1_3^2*t1_4^2/16 + 391*t1_1^5*t1_2*t1_3*t1_4^3/16 + 309*t1_1^5*t1_2*t1_4^4/128 + 47*t1_1^5*t1_3^5/4 + 235*t1_1^5*t1_3^4*t1_4/8 + 209*t1_1^5*t1_3^3*t1_4^2/8 + 157*t1_1^5*t1_3^2*t1_4^3/16 + 111*t1_1^5*t1_3*t1_4^4/64 + 27*t1_1^5*t1_4^5/128 + 15153*t1_1^4*t1_2^6/256 + 15153*t1_1^4*t1_2^5*t1_3/64 + 15153*t1_1^4*t1_2^5*t1_4/128 + 49715*t1_1^4*t1_2^4*t1_3^2/128 + 49715*t1_1^4*t1_2^4*t1_3*t1_4/128 + 23665*t1_1^4*t1_2^4*t1_4^2/256 + 5405*t1_1^4*t1_2^3*t1_3^3/16 + 16215*t1_1^4*t1_2^3*t1_3^2*t1_4/32 + 3725*t1_1^4*t1_2^3*t1_3*t1_4^2/16 + 2045*t1_1^4*t1_2^3*t1_4^3/64 + 1345*t1_1^4*t1_2^2*t1_3^4/8 + 1345*t1_1^4*t1_2^2*t1_3^3*t1_4/4 + 14505*t1_1^4*t1_2^2*t1_3^2*t1_4^2/64 + 3745*t1_1^4*t1_2^2*t1_3*t1_4^3/64 + 1355*t1_1^4*t1_2^2*t1_4^4/256 + 47*t1_1^4*t1_2*t1_3^5 + 235*t1_1^4*t1_2*t1_3^4*t1_4/2 + 1685*t1_1^4*t1_2*t1_3^3*t1_4^2/16 + 1295*t1_1^4*t1_2*t1_3^2*t1_4^3/32 + 455*t1_1^4*t1_2*t1_3*t1_4^4/64 + 93*t1_1^4*t1_2*t1_4^5/128 + 47*t1_1^4*t1_3^6/8 + 141*t1_1^4*t1_3^5*t1_4/8 + 20*t1_1^4*t1_3^4*t1_4^2 + 85*t1_1^4*t1_3^3*t1_4^3/8 + 355*t1_1^4*t1_3^2*t1_4^4/128 + 51*t1_1^4*t1_3*t1_4^5/128 + 3*t1_1^4*t1_4^6/256 + 159*t1_1^3*t1_2^7/4 + 371*t1_1^3*t1_2^6*t1_3/2 + 371*t1_1^3*t1_2^6*t1_4/4 + 11533*t1_1^3*t1_2^5*t1_3^2/32 + 11533*t1_1^3*t1_2^5*t1_3*t1_4/32 + 2629*t1_1^3*t1_2^5*t1_4^2/32 + 12073*t1_1^3*t1_2^4*t1_3^3/32 + 36219*t1_1^3*t1_2^4*t1_3^2*t1_4/64 + 16361*t1_1^3*t1_2^4*t1_3*t1_4^2/64 + 67*t1_1^3*t1_2^4*t1_4^3/2 + 1845*t1_1^3*t1_2^3*t1_3^4/8 + 1845*t1_1^3*t1_2^3*t1_3^3*t1_4/4 + 1245*t1_1^3*t1_2^3*t1_3^2*t1_4^2/4 + 645*t1_1^3*t1_2^3*t1_3*t1_4^3/8 + 109*t1_1^3*t1_2^3*t1_4^4/16 + 167*t1_1^3*t1_2^2*t1_3^5/2 + 835*t1_1^3*t1_2^2*t1_3^4*t1_4/4 + 3015*t1_1^3*t1_2^2*t1_3^3*t1_4^2/16 + 2365*t1_1^3*t1_2^2*t1_3^2*t1_4^3/32 + 407*t1_1^3*t1_2^2*t1_3*t1_4^4/32 + t1_1^3*t1_2^2*t1_4^5 + 17*t1_1^3*t1_2*t1_3^6 + 51*t1_1^3*t1_2*t1_3^5*t1_4 + 465*t1_1^3*t1_2*t1_3^4*t1_4^2/8 + 125*t1_1^3*t1_2*t1_3^3*t1_4^3/4 + 263*t1_1^3*t1_2*t1_3^2*t1_4^4/32 + 35*t1_1^3*t1_2*t1_3*t1_4^5/32 + t1_1^3*t1_2*t1_4^6/32 + 3*t1_1^3*t1_3^7/2 + 21*t1_1^3*t1_3^6*t1_4/4 + 29*t1_1^3*t1_3^5*t1_4^2/4 + 5*t1_1^3*t1_3^4*t1_4^3 + 57*t1_1^3*t1_3^3*t1_4^4/32 + 19*t1_1^3*t1_3^2*t1_4^5/64 + t1_1^3*t1_3*t1_4^6/64 + 2073*t1_1^2*t1_2^8/128 + 691*t1_1^2*t1_2^7*t1_3/8 + 691*t1_1^2*t1_2^7*t1_4/16 + 12471*t1_1^2*t1_2^6*t1_3^2/64 + 12471*t1_1^2*t1_2^6*t1_3*t1_4/64 + 2797*t1_1^2*t1_2^6*t1_4^2/64 + 3859*t1_1^2*t1_2^5*t1_3^3/16 + 11577*t1_1^2*t1_2^5*t1_3^2*t1_4/32 + 5205*t1_1^2*t1_2^5*t1_3*t1_4^2/32 + 673*t1_1^2*t1_2^5*t1_4^3/32 + 22737*t1_1^2*t1_2^4*t1_3^4/128 + 22737*t1_1^2*t1_2^4*t1_3^3*t1_4/64 + 30781*t1_1^2*t1_2^4*t1_3^2*t1_4^2/128 + 2011*t1_1^2*t1_2^4*t1_3*t1_4^3/32 + 657*t1_1^2*t1_2^4*t1_4^4/128 + 1263*t1_1^2*t1_2^3*t1_3^5/16 + 6315*t1_1^2*t1_2^3*t1_3^4*t1_4/32 + 1433*t1_1^2*t1_2^3*t1_3^3*t1_4^2/8 + 2283*t1_1^2*t1_2^3*t1_3^2*t1_4^3/32 + 193*t1_1^2*t1_2^3*t1_3*t1_4^4/16 + 23*t1_1^2*t1_2^3*t1_4^5/32 + 327*t1_1^2*t1_2^2*t1_3^6/16 + 981*t1_1^2*t1_2^2*t1_3^5*t1_4/16 + 4487*t1_1^2*t1_2^2*t1_3^4*t1_4^2/64 + 1217*t1_1^2*t1_2^2*t1_3^3*t1_4^3/32 + 319*t1_1^2*t1_2^2*t1_3^2*t1_4^4/32 + 75*t1_1^2*t1_2^2*t1_3*t1_4^5/64 + t1_1^2*t1_2^2*t1_4^6/32 + 11*t1_1^2*t1_2*t1_3^7/4 + 77*t1_1^2*t1_2*t1_3^6*t1_4/8 + 213*t1_1^2*t1_2*t1_3^5*t1_4^2/16 + 295*t1_1^2*t1_2*t1_3^4*t1_4^3/32 + 53*t1_1^2*t1_2*t1_3^3*t1_4^4/16 + 9*t1_1^2*t1_2*t1_3^2*t1_4^5/16 + t1_1^2*t1_2*t1_3*t1_4^6/32 + t1_1^2*t1_3^8/8 + t1_1^2*t1_3^7*t1_4/2 + 13*t1_1^2*t1_3^6*t1_4^2/16 + 11*t1_1^2*t1_3^5*t1_4^3/16 + 41*t1_1^2*t1_3^4*t1_4^4/128 + 5*t1_1^2*t1_3^3*t1_4^5/64 + t1_1^2*t1_3^2*t1_4^6/128 + 459*t1_1*t1_2^9/128 + 1377*t1_1*t1_2^8*t1_3/64 + 1377*t1_1*t1_2^8*t1_4/128 + 1773*t1_1*t1_2^7*t1_3^2/32 + 1773*t1_1*t1_2^7*t1_3*t1_4/32 + 99*t1_1*t1_2^7*t1_4^2/8 + 5099*t1_1*t1_2^6*t1_3^3/64 + 15297*t1_1*t1_2^6*t1_3^2*t1_4/128 + 6879*t1_1*t1_2^6*t1_3*t1_4^2/128 + 445*t1_1*t1_2^6*t1_4^3/64 + 8905*t1_1*t1_2^5*t1_3^4/128 + 8905*t1_1*t1_2^5*t1_3^3*t1_4/64 + 12093*t1_1*t1_2^5*t1_3^2*t1_4^2/128 + 797*t1_1*t1_2^5*t1_3*t1_4^3/32 + 259*t1_1*t1_2^5*t1_4^4/128 + 599*t1_1*t1_2^4*t1_3^5/16 + 2995*t1_1*t1_2^4*t1_3^4*t1_4/32 + 2729*t1_1*t1_2^4*t1_3^3*t1_4^2/32 + 2197*t1_1*t1_2^4*t1_3^2*t1_4^3/64 + 185*t1_1*t1_2^4*t1_3*t1_4^4/32 + 37*t1_1*t1_2^4*t1_4^5/128 + 191*t1_1*t1_2^3*t1_3^6/16 + 573*t1_1*t1_2^3*t1_3^5*t1_4/16 + 2627*t1_1*t1_2^3*t1_3^4*t1_4^2/64 + 717*t1_1*t1_2^3*t1_3^3*t1_4^3/32 + 375*t1_1*t1_2^3*t1_3^2*t1_4^4/64 + 5*t1_1*t1_2^3*t1_3*t1_4^5/8 + t1_1*t1_2^3*t1_4^6/64 + 2*t1_1*t1_2^2*t1_3^7 + 7*t1_1*t1_2^2*t1_3^6*t1_4 + 155*t1_1*t1_2^2*t1_3^5*t1_4^2/16 + 215*t1_1*t1_2^2*t1_3^4*t1_4^3/32 + 155*t1_1*t1_2^2*t1_3^3*t1_4^4/64 + 53*t1_1*t1_2^2*t1_3^2*t1_4^5/128 + 3*t1_1*t1_2^2*t1_3*t1_4^6/128 + t1_1*t1_2*t1_3^8/8 + t1_1*t1_2*t1_3^7*t1_4/2 + 13*t1_1*t1_2*t1_3^6*t1_4^2/16 + 11*t1_1*t1_2*t1_3^5*t1_4^3/16 + 41*t1_1*t1_2*t1_3^4*t1_4^4/128 + 5*t1_1*t1_2*t1_3^3*t1_4^5/64 + t1_1*t1_2*t1_3^2*t1_4^6/128 + 81*t1_2^10/256 + 135*t1_2^9*t1_3/64 + 135*t1_2^9*t1_4/128 + 783*t1_2^8*t1_3^2/128 + 783*t1_2^8*t1_3*t1_4/128 + 351*t1_2^8*t1_4^2/256 + 645*t1_2^7*t1_3^3/64 + 1935*t1_2^7*t1_3^2*t1_4/128 + 873*t1_2^7*t1_3*t1_4^2/128 + 57*t1_2^7*t1_4^3/64 + 2641*t1_2^6*t1_3^4/256 + 2641*t1_2^6*t1_3^3*t1_4/128 + 3597*t1_2^6*t1_3^2*t1_4^2/256 + 239*t1_2^6*t1_3*t1_4^3/64 + 79*t1_2^6*t1_4^4/256 + 215*t1_2^5*t1_3^5/32 + 1075*t1_2^5*t1_3^4*t1_4/64 + 491*t1_2^5*t1_3^3*t1_4^2/32 + 199*t1_2^5*t1_3^2*t1_4^3/32 + 17*t1_2^5*t1_3*t1_4^4/16 + 7*t1_2^5*t1_4^5/128 + 87*t1_2^4*t1_3^6/32 + 261*t1_2^4*t1_3^5*t1_4/32 + 1199*t1_2^4*t1_3^4*t1_4^2/128 + 329*t1_2^4*t1_3^3*t1_4^3/64 + 87*t1_2^4*t1_3^2*t1_4^4/64 + 19*t1_2^4*t1_3*t1_4^5/128 + t1_2^4*t1_4^6/256 + 5*t1_2^3*t1_3^7/8 + 35*t1_2^3*t1_3^6*t1_4/16 + 97*t1_2^3*t1_3^5*t1_4^2/32 + 135*t1_2^3*t1_3^4*t1_4^3/64 + 49*t1_2^3*t1_3^3*t1_4^4/64 + 17*t1_2^3*t1_3^2*t1_4^5/128 + t1_2^3*t1_3*t1_4^6/128 + t1_2^2*t1_3^8/16 + t1_2^2*t1_3^7*t1_4/4 + 13*t1_2^2*t1_3^6*t1_4^2/32 + 11*t1_2^2*t1_3^5*t1_4^3/32 + 41*t1_2^2*t1_3^4*t1_4^4/256 + 5*t1_2^2*t1_3^3*t1_4^5/128 + t1_2^2*t1_3^2*t1_4^6/256 by
    convert hleaf using 1 <;> ring
  positivity

theorem P27' {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a + b + c + d = 4) : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / d ^ 2) := by
  rw [← sub_nonneg]
  have hden1_pos : 0 < a := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd, h]
  have hden1_ne : a ≠ 0 := ne_of_gt hden1_pos
  have hden2_pos : 0 < b := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd, h]
  have hden2_ne : b ≠ 0 := ne_of_gt hden2_pos
  have hden3_pos : 0 < c := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd, h]
  have hden3_ne : c ≠ 0 := ne_of_gt hden3_pos
  have hden4_pos : 0 < d := by
    first
    | positivity
    | nlinarith [ha, hb, hc, hd, h]
  have hden4_ne : d ≠ 0 := ne_of_gt hden4_pos
  field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm, hd.ne.symm, hden1_pos, hden2_pos, hden3_pos, hden4_pos, hden1_ne, hden2_ne, hden3_ne, hden4_ne]
  ring_nf
  have hQ : a + b + c + d = 4 := by nlinarith [h]
  have hQunit : a/4 + b/4 + c/4 + d/4 = 1 := by nlinarith [hQ]
  suffices hH :
      0 ≤ -a^4*b^2*c^2*d^2 - a^2*b^4*c^2*d^2 - a^2*b^2*c^4*d^2 - a^2*b^2*c^2*d^4 + a^2*b^2*c^2*(a/4 + b/4 + c/4 + d/4)^4 + a^2*b^2*d^2*(a/4 + b/4 + c/4 + d/4)^4 + a^2*c^2*d^2*(a/4 + b/4 + c/4 + d/4)^4 + b^2*c^2*d^2*(a/4 + b/4 + c/4 + d/4)^4 by
    convert hH using 1
    try rw [hQunit]
    try rw [hQ]
    ring_nf
  ring_nf
  clear h hQ hQunit
  clear hden1_pos hden2_pos hden3_pos hden4_pos hden1_ne hden2_ne hden3_ne hden4_ne
  have hDS_class_1 := private_hDS_class_1
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
          have hcert := hDS_class_1 c d b a (by positivity) (by positivity) (by positivity) (by positivity) hs
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
            have hcert := hDS_class_1 c b d a (by positivity) (by positivity) (by positivity) (by positivity) hs
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
          have hcert := hDS_class_1 d b c a (by positivity) (by positivity) (by positivity) (by positivity) hs
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
            have hcert := hDS_class_1 b d c a (by positivity) (by positivity) (by positivity) (by positivity) hs
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
              have hcert := hDS_class_1 b c a d (by positivity) (by positivity) (by positivity) (by positivity) hs
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
          have hcert := hDS_class_1 d b a c (by positivity) (by positivity) (by positivity) (by positivity) hs
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
            have hcert := hDS_class_1 b d a c (by positivity) (by positivity) (by positivity) (by positivity) hs
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
              have hcert := hDS_class_1 b a c d (by positivity) (by positivity) (by positivity) (by positivity) hs
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
        have hcert := hDS_class_1 d c a b (by positivity) (by positivity) (by positivity) (by positivity) hs
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
            have hcert := hDS_class_1 c a d b (by positivity) (by positivity) (by positivity) (by positivity) hs
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
            have hcert := hDS_class_1 c a b d (by positivity) (by positivity) (by positivity) (by positivity) hs
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
          have hcert := hDS_class_1 d a c b (by positivity) (by positivity) (by positivity) (by positivity) hs
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
              have hcert := hDS_class_1 a c d b (by positivity) (by positivity) (by positivity) (by positivity) hs
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
              have hcert := hDS_class_1 a c b d (by positivity) (by positivity) (by positivity) (by positivity) hs
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
            have hcert := hDS_class_1 a d b c (by positivity) (by positivity) (by positivity) (by positivity) hs
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
              have hcert := hDS_class_1 a b d c (by positivity) (by positivity) (by positivity) (by positivity) hs
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



theorem P27 {a b c d : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h : a + b + c + d = 4) : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≤ 1 / a ^ 2 + 1 / b ^ 2 + 1 / c ^ 2 + 1 / d ^ 2) := by
  exact @P27' a b c d ha hb hc hd h
