import Mathlib
import Dittert4.DH4OneDiv52FastPolyCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-!
# FastPoly proof of Theorem 1.2 and Theorem 1.1 for DH4

This main file keeps the matrix notation and the final paper-style theorems.
The exact SOS certificate is checked by the FastPoly verifier in `DH4OneDiv52FastPolyCertificate`.
-/

noncomputable section

abbrev Matrix4 := Fin 4 → Fin 4 → ℝ

def K4 : Set Matrix4 :=
  { A | (∀ i j, 0 ≤ A i j) ∧
    A (0 : Fin 4) (0 : Fin 4) + A (0 : Fin 4) (1 : Fin 4) + A (0 : Fin 4) (2 : Fin 4) + A (0 : Fin 4) (3 : Fin 4) + A (1 : Fin 4) (0 : Fin 4) + A (1 : Fin 4) (1 : Fin 4) + A (1 : Fin 4) (2 : Fin 4) + A (1 : Fin 4) (3 : Fin 4) + A (2 : Fin 4) (0 : Fin 4) + A (2 : Fin 4) (1 : Fin 4) + A (2 : Fin 4) (2 : Fin 4) + A (2 : Fin 4) (3 : Fin 4) + A (3 : Fin 4) (0 : Fin 4) + A (3 : Fin 4) (1 : Fin 4) + A (3 : Fin 4) (2 : Fin 4) + A (3 : Fin 4) (3 : Fin 4) = 4
  }

def U4 : Matrix4 :=
  fun _ _ => (1 / 4 : ℝ)

private def row_product_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ)
    : ℝ :=
  ((a11 + a12 + a13 + a14) * (a21 + a22 + a23 + a24) *
    (a31 + a32 + a33 + a34) * (a41 + a42 + a43 + a44))

private def column_product_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ)
    : ℝ :=
  ((a11 + a21 + a31 + a41) * (a12 + a22 + a32 + a42) *
    (a13 + a23 + a33 + a43) * (a14 + a24 + a34 + a44))

private def matrix_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  ![![a11, a12, a13, a14],
    ![a21, a22, a23, a24],
    ![a31, a32, a33, a34],
    ![a41, a42, a43, a44]]

private def permanent_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ)
    : ℝ :=
  Matrix.permanent
    (matrix_entries a11 a12 a13 a14 a21 a22 a23 a24
      a31 a32 a33 a34 a41 a42 a43 a44)

private theorem matrix_permanent_eq_permanent_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) :
    Matrix.permanent
      ![![a11, a12, a13, a14],
        ![a21, a22, a23, a24],
        ![a31, a32, a33, a34],
        ![a41, a42, a43, a44]] =
      permanent_entries a11 a12 a13 a14 a21 a22 a23 a24
        a31 a32 a33 a34 a41 a42 a43 a44 := by
  rfl

private theorem permanent_entries_eq_fast_poly
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) :
    permanent_entries a11 a12 a13 a14 a21 a22 a23 a24
        a31 a32 a33 a34 a41 a42 a43 a44 =
      SparsePolyCheck.eval
        (DH4OneDiv52FastPolyCertificate.point
          a11 a12 a13 a14 a21 a22 a23 a24
          a31 a32 a33 a34 a41 a42 a43 a44)
        DH4OneDiv52FastPolyCertificate.permanentPoly := by
  rw [← matrix_permanent_eq_permanent_entries]
  let perms4 : Finset (Equiv.Perm (Fin 4)) :=
    ⟨permsOfList ([0, 1, 2, 3] : List (Fin 4)), by native_decide⟩
  have univ_perm4 :
      (Finset.univ : Finset (Equiv.Perm (Fin 4))) = perms4 := by
    native_decide
  rw [Matrix.permanent, univ_perm4]
  simp_rw [Fin.prod_univ_succ]
  simp [perms4, permsOfList,
    DH4OneDiv52FastPolyCertificate.permanentPoly,
    DH4OneDiv52FastPolyCertificate.polySum, DH4OneDiv52FastPolyCertificate.generator,
    DH4OneDiv52FastPolyCertificate.point, Equiv.swap_apply_def, Matrix.cons_val]
  ring_nf

private def φ_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ)
    : ℝ :=
  row_product_entries a11 a12 a13 a14 a21 a22 a23 a24
    a31 a32 a33 a34 a41 a42 a43 a44
  + column_product_entries a11 a12 a13 a14 a21 a22 a23 a24
    a31 a32 a33 a34 a41 a42 a43 a44
  - permanent_entries a11 a12 a13 a14 a21 a22 a23 a24
    a31 a32 a33 a34 a41 a42 a43 a44

/-- The Dittert function phi(A). -/
def φ (A : Matrix4) : ℝ :=
  φ_entries (A (0 : Fin 4) (0 : Fin 4)) (A (0 : Fin 4) (1 : Fin 4)) (A (0 : Fin 4) (2 : Fin 4)) (A (0 : Fin 4) (3 : Fin 4)) (A (1 : Fin 4) (0 : Fin 4)) (A (1 : Fin 4) (1 : Fin 4)) (A (1 : Fin 4) (2 : Fin 4)) (A (1 : Fin 4) (3 : Fin 4)) (A (2 : Fin 4) (0 : Fin 4)) (A (2 : Fin 4) (1 : Fin 4)) (A (2 : Fin 4) (2 : Fin 4)) (A (2 : Fin 4) (3 : Fin 4)) (A (3 : Fin 4) (0 : Fin 4)) (A (3 : Fin 4) (1 : Fin 4)) (A (3 : Fin 4) (2 : Fin 4)) (A (3 : Fin 4) (3 : Fin 4))

private theorem phi_U4_eq :
    φ U4 = 61 / 32 := by
  unfold φ φ_entries row_product_entries column_product_entries U4
  rw [show permanent_entries (1 / 4) (1 / 4) (1 / 4) (1 / 4)
      (1 / 4) (1 / 4) (1 / 4) (1 / 4)
      (1 / 4) (1 / 4) (1 / 4) (1 / 4)
      (1 / 4) (1 / 4) (1 / 4) (1 / 4) =
        SparsePolyCheck.eval
          (DH4OneDiv52FastPolyCertificate.point
            (1 / 4) (1 / 4) (1 / 4) (1 / 4)
            (1 / 4) (1 / 4) (1 / 4) (1 / 4)
            (1 / 4) (1 / 4) (1 / 4) (1 / 4)
            (1 / 4) (1 / 4) (1 / 4) (1 / 4))
          DH4OneDiv52FastPolyCertificate.permanentPoly by
    exact permanent_entries_eq_fast_poly
      (1 / 4) (1 / 4) (1 / 4) (1 / 4)
      (1 / 4) (1 / 4) (1 / 4) (1 / 4)
      (1 / 4) (1 / 4) (1 / 4) (1 / 4)
      (1 / 4) (1 / 4) (1 / 4) (1 / 4)]
  norm_num [DH4OneDiv52FastPolyCertificate.permanentPoly,
    DH4OneDiv52FastPolyCertificate.polySum, DH4OneDiv52FastPolyCertificate.generator,
    DH4OneDiv52FastPolyCertificate.point]

private def frobenius_distance_to_U4_squared_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ)
    : ℝ :=
  (a11 - 1 / 4) ^ 2
  + (a12 - 1 / 4) ^ 2
  + (a13 - 1 / 4) ^ 2
  + (a14 - 1 / 4) ^ 2
  + (a21 - 1 / 4) ^ 2
  + (a22 - 1 / 4) ^ 2
  + (a23 - 1 / 4) ^ 2
  + (a24 - 1 / 4) ^ 2
  + (a31 - 1 / 4) ^ 2
  + (a32 - 1 / 4) ^ 2
  + (a33 - 1 / 4) ^ 2
  + (a34 - 1 / 4) ^ 2
  + (a41 - 1 / 4) ^ 2
  + (a42 - 1 / 4) ^ 2
  + (a43 - 1 / 4) ^ 2
  + (a44 - 1 / 4) ^ 2

private def frobenius_norm_squared_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ)
    : ℝ :=
  a11 ^ 2
  + a12 ^ 2
  + a13 ^ 2
  + a14 ^ 2
  + a21 ^ 2
  + a22 ^ 2
  + a23 ^ 2
  + a24 ^ 2
  + a31 ^ 2
  + a32 ^ 2
  + a33 ^ 2
  + a34 ^ 2
  + a41 ^ 2
  + a42 ^ 2
  + a43 ^ 2
  + a44 ^ 2

/-- The squared Frobenius norm. Thus `‖A - U4‖_F^2` is `||A - U4||_F^2`. -/
def frobenius_norm_squared (A : Matrix4) : ℝ :=
  frobenius_norm_squared_entries (A (0 : Fin 4) (0 : Fin 4)) (A (0 : Fin 4) (1 : Fin 4)) (A (0 : Fin 4) (2 : Fin 4)) (A (0 : Fin 4) (3 : Fin 4)) (A (1 : Fin 4) (0 : Fin 4)) (A (1 : Fin 4) (1 : Fin 4)) (A (1 : Fin 4) (2 : Fin 4)) (A (1 : Fin 4) (3 : Fin 4)) (A (2 : Fin 4) (0 : Fin 4)) (A (2 : Fin 4) (1 : Fin 4)) (A (2 : Fin 4) (2 : Fin 4)) (A (2 : Fin 4) (3 : Fin 4)) (A (3 : Fin 4) (0 : Fin 4)) (A (3 : Fin 4) (1 : Fin 4)) (A (3 : Fin 4) (2 : Fin 4)) (A (3 : Fin 4) (3 : Fin 4))

notation "‖" A "‖_F^2" => frobenius_norm_squared A

private theorem fast_DH4_entries_eq
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) :
    DH4OneDiv52FastPolyCertificate.DH4 a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 =
      (61 / 32 : ℝ) - φ_entries a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 := by
  unfold φ_entries
  rw [permanent_entries_eq_fast_poly]
  norm_num [DH4OneDiv52FastPolyCertificate.DH4,
    DH4OneDiv52FastPolyCertificate.dh4IntegerPoly,
    DH4OneDiv52FastPolyCertificate.rowProductPoly, DH4OneDiv52FastPolyCertificate.columnProductPoly,
    DH4OneDiv52FastPolyCertificate.row0, DH4OneDiv52FastPolyCertificate.row1, DH4OneDiv52FastPolyCertificate.row2, DH4OneDiv52FastPolyCertificate.row3,
    DH4OneDiv52FastPolyCertificate.column0, DH4OneDiv52FastPolyCertificate.column1, DH4OneDiv52FastPolyCertificate.column2, DH4OneDiv52FastPolyCertificate.column3,
    DH4OneDiv52FastPolyCertificate.permanentPoly, DH4OneDiv52FastPolyCertificate.polyProduct, DH4OneDiv52FastPolyCertificate.polySum,
    DH4OneDiv52FastPolyCertificate.generator, row_product_entries,
    column_product_entries, DH4OneDiv52FastPolyCertificate.point]
  ring_nf

private theorem fast_D4_entries_eq
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) :
    DH4OneDiv52FastPolyCertificate.D4 a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 =
      frobenius_distance_to_U4_squared_entries a11 a12 a13 a14 a21 a22 a23 a24 a31 a32 a33 a34 a41 a42 a43 a44 := by
  norm_num [DH4OneDiv52FastPolyCertificate.D4,
    DH4OneDiv52FastPolyCertificate.d4Poly, DH4OneDiv52FastPolyCertificate.centeredSquare,
    DH4OneDiv52FastPolyCertificate.polySum, frobenius_distance_to_U4_squared_entries,
    DH4OneDiv52FastPolyCertificate.point]
  ring_nf

private theorem frobenius_norm_squared_nonneg (A : Matrix4) :
    0 ≤ ‖A‖_F^2 := by
  unfold frobenius_norm_squared frobenius_norm_squared_entries
  positivity

private theorem frobenius_norm_squared_sub_U4_eq_zero_iff (A : Matrix4) :
    ‖A - U4‖_F^2 = 0 ↔ A = U4 := by
  constructor
  · intro hdist
    have hdist_entries :
        frobenius_distance_to_U4_squared_entries (A (0 : Fin 4) (0 : Fin 4)) (A (0 : Fin 4) (1 : Fin 4)) (A (0 : Fin 4) (2 : Fin 4)) (A (0 : Fin 4) (3 : Fin 4)) (A (1 : Fin 4) (0 : Fin 4)) (A (1 : Fin 4) (1 : Fin 4)) (A (1 : Fin 4) (2 : Fin 4)) (A (1 : Fin 4) (3 : Fin 4)) (A (2 : Fin 4) (0 : Fin 4)) (A (2 : Fin 4) (1 : Fin 4)) (A (2 : Fin 4) (2 : Fin 4)) (A (2 : Fin 4) (3 : Fin 4)) (A (3 : Fin 4) (0 : Fin 4)) (A (3 : Fin 4) (1 : Fin 4)) (A (3 : Fin 4) (2 : Fin 4)) (A (3 : Fin 4) (3 : Fin 4)) = 0 := by
      simpa [frobenius_norm_squared, frobenius_norm_squared_entries,
        frobenius_distance_to_U4_squared_entries, U4] using hdist
    have hD4 :
        DH4OneDiv52FastPolyCertificate.D4
          (A (0 : Fin 4) (0 : Fin 4)) (A (0 : Fin 4) (1 : Fin 4)) (A (0 : Fin 4) (2 : Fin 4)) (A (0 : Fin 4) (3 : Fin 4)) (A (1 : Fin 4) (0 : Fin 4)) (A (1 : Fin 4) (1 : Fin 4)) (A (1 : Fin 4) (2 : Fin 4)) (A (1 : Fin 4) (3 : Fin 4)) (A (2 : Fin 4) (0 : Fin 4)) (A (2 : Fin 4) (1 : Fin 4)) (A (2 : Fin 4) (2 : Fin 4)) (A (2 : Fin 4) (3 : Fin 4)) (A (3 : Fin 4) (0 : Fin 4)) (A (3 : Fin 4) (1 : Fin 4)) (A (3 : Fin 4) (2 : Fin 4)) (A (3 : Fin 4) (3 : Fin 4)) = 0 := by
      rw [fast_D4_entries_eq]
      exact hdist_entries
    have hentries := (DH4OneDiv52FastPolyCertificate.D4_eq_zero_iff
      (A (0 : Fin 4) (0 : Fin 4)) (A (0 : Fin 4) (1 : Fin 4)) (A (0 : Fin 4) (2 : Fin 4)) (A (0 : Fin 4) (3 : Fin 4)) (A (1 : Fin 4) (0 : Fin 4)) (A (1 : Fin 4) (1 : Fin 4)) (A (1 : Fin 4) (2 : Fin 4)) (A (1 : Fin 4) (3 : Fin 4)) (A (2 : Fin 4) (0 : Fin 4)) (A (2 : Fin 4) (1 : Fin 4)) (A (2 : Fin 4) (2 : Fin 4)) (A (2 : Fin 4) (3 : Fin 4)) (A (3 : Fin 4) (0 : Fin 4)) (A (3 : Fin 4) (1 : Fin 4)) (A (3 : Fin 4) (2 : Fin 4)) (A (3 : Fin 4) (3 : Fin 4))).mp hD4
    rcases hentries with ⟨ha11, ha12, ha13, ha14, ha21, ha22, ha23, ha24,
      ha31, ha32, ha33, ha34, ha41, ha42, ha43, ha44⟩
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [U4, ha11, ha12, ha13, ha14, ha21, ha22, ha23, ha24,
        ha31, ha32, ha33, ha34, ha41, ha42, ha43, ha44]
  · intro hA
    subst A
    unfold frobenius_norm_squared frobenius_norm_squared_entries U4
    norm_num

/--
Theorem 1.2, informal statement.

This is the quantitative stability estimate used to prove the Dittert
conjecture in dimension 4.

Here `K4` is the simplex of all `4 × 4` real matrices with nonnegative entries
and total sum equal to `4`.  The matrix `U4` is the uniform matrix whose sixteen
entries are all `1 / 4`.  The function `φ` is the Dittert functional:
the product of the four row sums, plus the product of the four column sums,
minus the permanent.

The theorem says that every matrix `A` in `K4` satisfies a stronger estimate
than just `φ A ≤ 61 / 32`: the gap from the optimal value controls the squared
Frobenius distance from `A` to the uniform matrix `U4`.  In words, if `A` moves
away from `U4`, then the value of `φ A` must drop by at least
`(1 / 52) * ‖A - U4‖_F^2`.

-/

theorem theorem_1_2_quantitative_stability_for_DH4
    (A : Matrix4) (hA : A ∈ K4) :
    (61 / 32 : ℝ) - φ A ≥ (1 / 52 : ℝ) * ‖A - U4‖_F^2 := by
  rcases hA with ⟨h_nonneg, hsum⟩
  have h1 : 0 ≤ A (0 : Fin 4) (0 : Fin 4) := h_nonneg _ _
  have h2 : 0 ≤ A (0 : Fin 4) (1 : Fin 4) := h_nonneg _ _
  have h3 : 0 ≤ A (0 : Fin 4) (2 : Fin 4) := h_nonneg _ _
  have h4 : 0 ≤ A (0 : Fin 4) (3 : Fin 4) := h_nonneg _ _
  have h5 : 0 ≤ A (1 : Fin 4) (0 : Fin 4) := h_nonneg _ _
  have h6 : 0 ≤ A (1 : Fin 4) (1 : Fin 4) := h_nonneg _ _
  have h7 : 0 ≤ A (1 : Fin 4) (2 : Fin 4) := h_nonneg _ _
  have h8 : 0 ≤ A (1 : Fin 4) (3 : Fin 4) := h_nonneg _ _
  have h9 : 0 ≤ A (2 : Fin 4) (0 : Fin 4) := h_nonneg _ _
  have h10 : 0 ≤ A (2 : Fin 4) (1 : Fin 4) := h_nonneg _ _
  have h11 : 0 ≤ A (2 : Fin 4) (2 : Fin 4) := h_nonneg _ _
  have h12 : 0 ≤ A (2 : Fin 4) (3 : Fin 4) := h_nonneg _ _
  have h13 : 0 ≤ A (3 : Fin 4) (0 : Fin 4) := h_nonneg _ _
  have h14 : 0 ≤ A (3 : Fin 4) (1 : Fin 4) := h_nonneg _ _
  have h15 : 0 ≤ A (3 : Fin 4) (2 : Fin 4) := h_nonneg _ _
  have h16 : 0 ≤ A (3 : Fin 4) (3 : Fin 4) := h_nonneg _ _
  have htarget := DH4OneDiv52FastPolyCertificate.DH4_one_div_52_sos (A (0 : Fin 4) (0 : Fin 4)) (A (0 : Fin 4) (1 : Fin 4)) (A (0 : Fin 4) (2 : Fin 4)) (A (0 : Fin 4) (3 : Fin 4)) (A (1 : Fin 4) (0 : Fin 4)) (A (1 : Fin 4) (1 : Fin 4)) (A (1 : Fin 4) (2 : Fin 4)) (A (1 : Fin 4) (3 : Fin 4)) (A (2 : Fin 4) (0 : Fin 4)) (A (2 : Fin 4) (1 : Fin 4)) (A (2 : Fin 4) (2 : Fin 4)) (A (2 : Fin 4) (3 : Fin 4)) (A (3 : Fin 4) (0 : Fin 4)) (A (3 : Fin 4) (1 : Fin 4)) (A (3 : Fin 4) (2 : Fin 4)) (A (3 : Fin 4) (3 : Fin 4)) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 hsum
  rw [fast_DH4_entries_eq, fast_D4_entries_eq] at htarget
  have hstable_entries :
      (61 / 32 : ℝ) - φ_entries (A (0 : Fin 4) (0 : Fin 4)) (A (0 : Fin 4) (1 : Fin 4)) (A (0 : Fin 4) (2 : Fin 4)) (A (0 : Fin 4) (3 : Fin 4)) (A (1 : Fin 4) (0 : Fin 4)) (A (1 : Fin 4) (1 : Fin 4)) (A (1 : Fin 4) (2 : Fin 4)) (A (1 : Fin 4) (3 : Fin 4)) (A (2 : Fin 4) (0 : Fin 4)) (A (2 : Fin 4) (1 : Fin 4)) (A (2 : Fin 4) (2 : Fin 4)) (A (2 : Fin 4) (3 : Fin 4)) (A (3 : Fin 4) (0 : Fin 4)) (A (3 : Fin 4) (1 : Fin 4)) (A (3 : Fin 4) (2 : Fin 4)) (A (3 : Fin 4) (3 : Fin 4)) ≥
        (1 / 52 : ℝ) * frobenius_distance_to_U4_squared_entries (A (0 : Fin 4) (0 : Fin 4)) (A (0 : Fin 4) (1 : Fin 4)) (A (0 : Fin 4) (2 : Fin 4)) (A (0 : Fin 4) (3 : Fin 4)) (A (1 : Fin 4) (0 : Fin 4)) (A (1 : Fin 4) (1 : Fin 4)) (A (1 : Fin 4) (2 : Fin 4)) (A (1 : Fin 4) (3 : Fin 4)) (A (2 : Fin 4) (0 : Fin 4)) (A (2 : Fin 4) (1 : Fin 4)) (A (2 : Fin 4) (2 : Fin 4)) (A (2 : Fin 4) (3 : Fin 4)) (A (3 : Fin 4) (0 : Fin 4)) (A (3 : Fin 4) (1 : Fin 4)) (A (3 : Fin 4) (2 : Fin 4)) (A (3 : Fin 4) (3 : Fin 4)) := by
    linarith
  simpa [φ, frobenius_norm_squared, frobenius_norm_squared_entries,
    frobenius_distance_to_U4_squared_entries, U4] using hstable_entries

/--
Theorem 1.1, informal statement.

This is the Dittert conjecture in dimension 4, together with the uniqueness of
the equality case.

For a matrix `A ∈ K4`, the Dittert functional `φ A` is the product of the row
sums plus the product of the column sums minus the permanent of `A`.  The
uniform matrix `U4`, with every entry equal to `1 / 4`, has value
`φ U4 = 61 / 32`.

The theorem proves that `61 / 32` is the global maximum of `φ` on `K4`: every
admissible matrix satisfies `φ A ≤ 61 / 32`.  It also proves that equality
`φ A = 61 / 32` holds exactly when `A = U4`, equivalently when all sixteen
entries of `A` are equal to `1 / 4`.

The proof below derives this qualitative maximum statement from the stronger
stability estimate in Theorem 1.2.  If equality holds, the stability estimate
forces the Frobenius distance from `A` to `U4` to be zero, hence `A = U4`.
-/

theorem theorem_1_1_dittert_conjecture_dimension_four
    (A : Matrix4) (hA : A ∈ K4) :
    φ A ≤ 61 / 32 ∧ (φ A = 61 / 32 ↔ A = U4) := by
  constructor
  · have hstable := theorem_1_2_quantitative_stability_for_DH4
      A hA
    have hdist_nonneg := frobenius_norm_squared_nonneg (A - U4)
    linarith
  · constructor
    · intro hphi
      have hstable := theorem_1_2_quantitative_stability_for_DH4
        A hA
      have hdist_nonneg := frobenius_norm_squared_nonneg (A - U4)
      have hdist_zero : ‖A - U4‖_F^2 = 0 := by
        linarith
      exact (frobenius_norm_squared_sub_U4_eq_zero_iff A).mp hdist_zero
    · intro hAeq
      subst A
      exact phi_U4_eq

end
