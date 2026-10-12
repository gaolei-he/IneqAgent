import Mathlib

lemma sqrt_mul_sum_sqrt_mul_le {x y z w : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    √(x * y) + √(z * w) ≤ √((x + z) * (y + w)) := by
  let f : Bool → ℝ := fun i => if i then x else z
  let g : Bool → ℝ := fun i => if i then y else w
  have hf : ∀ i : Bool, 0 ≤ f i := by
    intro i
    by_cases hi : i
    · simp [f, hi, hx]
    · simp [f, hi, hz]
  have hg : ∀ i : Bool, 0 ≤ g i := by
    intro i
    by_cases hi : i
    · simp [g, hi, hy]
    · simp [g, hi, hw]
  have hcs := Real.sum_sqrt_mul_sqrt_le (s := (Finset.univ : Finset Bool)) (f := f) (g := g) hf hg
  have hsum_f : (∑ i : Bool, f i) = x + z := by
    simp [f]
  have hsum_g : (∑ i : Bool, g i) = y + w := by
    simp [g]
  have hleft : √(x * y) + √(z * w) = ∑ i : Bool, √(f i) * √(g i) := by
    simp [f, g, Real.sqrt_mul hx, Real.sqrt_mul hz]
  rw [← hleft, hsum_f, hsum_g] at hcs
  have hxz : 0 ≤ x + z := by positivity
  have hprod : √((x + z) * (y + w)) = √(x + z) * √(y + w) := by
    rw [Real.sqrt_mul hxz]
  rwa [hprod]

lemma mul_complement_sum_le_one {b c : ℝ} (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hb1 : b ≤ 1) (hc1 : c ≤ 1) : b * c + (1 - b) * (1 - c) ≤ 1 := by
  have hb1c : 0 ≤ b * (1 - c) := by positivity
  have hc1b : 0 ≤ c * (1 - b) := by positivity
  have hid : b * c + (1 - b) * (1 - c) = 1 - (b * (1 - c) + c * (1 - b)) := by ring
  nlinarith

theorem real_p34 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (ha1 : a < 1) (hb1 : b < 1) (hc1 : c < 1) : √(a * b * c) + √((1 - a) * (1 - b) * (1 - c)) ≤ 1 := by
  have ha0 : 0 ≤ a := le_of_lt ha
  have hb0 : 0 ≤ b := le_of_lt hb
  have hc0 : 0 ≤ c := le_of_lt hc
  have h1ma : 0 ≤ 1 - a := by linarith
  have h1mb : 0 ≤ 1 - b := by linarith
  have h1mc : 0 ≤ 1 - c := by linarith
  have hbc0 : 0 ≤ b * c := by positivity
  have h1mbc : 0 ≤ (1 - b) * (1 - c) := mul_nonneg h1mb h1mc
  have hcauchy := sqrt_mul_sum_sqrt_mul_le ha0 hbc0 h1ma h1mbc
  have hpair : b * c + (1 - b) * (1 - c) ≤ 1 := by
    exact mul_complement_sum_le_one hb0 hc0 (le_of_lt hb1) (le_of_lt hc1)
  calc
    √(a * b * c) + √((1 - a) * (1 - b) * (1 - c))
        ≤ √((a + (1 - a)) * (b * c + (1 - b) * (1 - c))) := by
          simpa [mul_assoc] using hcauchy
    _ ≤ √(b * c + (1 - b) * (1 - c)) := by
          have hsuma : a + (1 - a) = 1 := by ring
          have harg : (a + (1 - a)) * (b * c + (1 - b) * (1 - c))
              ≤ b * c + (1 - b) * (1 - c) := by
            simp [hsuma]
          exact Real.sqrt_le_sqrt harg
    _ ≤ 1 := Real.sqrt_le_one.mpr hpair
