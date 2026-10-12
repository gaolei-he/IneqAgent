import Dittert5.DH5GramEvaluation
import Dittert5.DH5ClassCoefficientAudit

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-!
# Exact Gram-matrix proof of Theorem 1.2 and Theorem 1.1 for DH5

This main file keeps the matrix notation and the final paper-style theorems.
The exact strengthened SOS certificate is checked below using the 325 by 325
Gram matrix and its exact class-coefficient audit.
-/

noncomputable section

namespace DH5Main

open scoped BigOperators
open DH5GramData DH5Symmetry DH5Coefficient DH5OrbitSum DH5PSD DH5GramEvaluation
open DH5ClassCoefficientAudit
open SparsePolyCheck

abbrev Matrix5 := Fin 5 → Fin 5 → ℝ

def K5 : Set Matrix5 :=
  { A | (∀ i j, 0 ≤ A i j) ∧
    A (0 : Fin 5) (0 : Fin 5) + A (0 : Fin 5) (1 : Fin 5) + A (0 : Fin 5) (2 : Fin 5) + A (0 : Fin 5) (3 : Fin 5) + A (0 : Fin 5) (4 : Fin 5) + A (1 : Fin 5) (0 : Fin 5) + A (1 : Fin 5) (1 : Fin 5) + A (1 : Fin 5) (2 : Fin 5) + A (1 : Fin 5) (3 : Fin 5) + A (1 : Fin 5) (4 : Fin 5) + A (2 : Fin 5) (0 : Fin 5) + A (2 : Fin 5) (1 : Fin 5) + A (2 : Fin 5) (2 : Fin 5) + A (2 : Fin 5) (3 : Fin 5) + A (2 : Fin 5) (4 : Fin 5) + A (3 : Fin 5) (0 : Fin 5) + A (3 : Fin 5) (1 : Fin 5) + A (3 : Fin 5) (2 : Fin 5) + A (3 : Fin 5) (3 : Fin 5) + A (3 : Fin 5) (4 : Fin 5) + A (4 : Fin 5) (0 : Fin 5) + A (4 : Fin 5) (1 : Fin 5) + A (4 : Fin 5) (2 : Fin 5) + A (4 : Fin 5) (3 : Fin 5) + A (4 : Fin 5) (4 : Fin 5) = 5
  }

def U5 : Matrix5 :=
  fun _ _ => (1 / 5 : ℝ)

private def row_product_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ) (a15 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ) (a25 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ) (a35 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) (a45 : ℝ)
    (a51 : ℝ) (a52 : ℝ) (a53 : ℝ) (a54 : ℝ) (a55 : ℝ)
    : ℝ :=
  ((a11 + a12 + a13 + a14 + a15) * (a21 + a22 + a23 + a24 + a25) *
    (a31 + a32 + a33 + a34 + a35) * (a41 + a42 + a43 + a44 + a45) *
    (a51 + a52 + a53 + a54 + a55))

private def column_product_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ) (a15 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ) (a25 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ) (a35 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) (a45 : ℝ)
    (a51 : ℝ) (a52 : ℝ) (a53 : ℝ) (a54 : ℝ) (a55 : ℝ)
    : ℝ :=
  ((a11 + a21 + a31 + a41 + a51) * (a12 + a22 + a32 + a42 + a52) *
    (a13 + a23 + a33 + a43 + a53) * (a14 + a24 + a34 + a44 + a54) *
    (a15 + a25 + a35 + a45 + a55))

private def matrix_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ) (a15 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ) (a25 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ) (a35 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) (a45 : ℝ)
    (a51 : ℝ) (a52 : ℝ) (a53 : ℝ) (a54 : ℝ) (a55 : ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  ![![a11, a12, a13, a14, a15],
    ![a21, a22, a23, a24, a25],
    ![a31, a32, a33, a34, a35],
    ![a41, a42, a43, a44, a45],
    ![a51, a52, a53, a54, a55]]

private def permanent_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ) (a15 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ) (a25 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ) (a35 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) (a45 : ℝ)
    (a51 : ℝ) (a52 : ℝ) (a53 : ℝ) (a54 : ℝ) (a55 : ℝ)
    : ℝ :=
  Matrix.permanent
    (matrix_entries a11 a12 a13 a14 a15 a21 a22 a23 a24 a25
      a31 a32 a33 a34 a35 a41 a42 a43 a44 a45 a51 a52 a53 a54 a55)

private theorem matrix_permanent_eq_permanent_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ) (a15 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ) (a25 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ) (a35 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) (a45 : ℝ)
    (a51 : ℝ) (a52 : ℝ) (a53 : ℝ) (a54 : ℝ) (a55 : ℝ) :
    Matrix.permanent
      ![![a11, a12, a13, a14, a15],
        ![a21, a22, a23, a24, a25],
        ![a31, a32, a33, a34, a35],
        ![a41, a42, a43, a44, a45],
        ![a51, a52, a53, a54, a55]] =
      permanent_entries a11 a12 a13 a14 a15 a21 a22 a23 a24 a25
        a31 a32 a33 a34 a35 a41 a42 a43 a44 a45 a51 a52 a53 a54 a55 := by
  rfl

private def φ_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ) (a15 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ) (a25 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ) (a35 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) (a45 : ℝ)
    (a51 : ℝ) (a52 : ℝ) (a53 : ℝ) (a54 : ℝ) (a55 : ℝ)
    : ℝ :=
  row_product_entries a11 a12 a13 a14 a15 a21 a22 a23 a24 a25
    a31 a32 a33 a34 a35 a41 a42 a43 a44 a45 a51 a52 a53 a54 a55
  + column_product_entries a11 a12 a13 a14 a15 a21 a22 a23 a24 a25
    a31 a32 a33 a34 a35 a41 a42 a43 a44 a45 a51 a52 a53 a54 a55
  - permanent_entries a11 a12 a13 a14 a15 a21 a22 a23 a24 a25
    a31 a32 a33 a34 a35 a41 a42 a43 a44 a45 a51 a52 a53 a54 a55

/-- The Dittert function phi(A). -/
def φ (A : Matrix5) : ℝ :=
  φ_entries (A (0 : Fin 5) (0 : Fin 5)) (A (0 : Fin 5) (1 : Fin 5)) (A (0 : Fin 5) (2 : Fin 5)) (A (0 : Fin 5) (3 : Fin 5)) (A (0 : Fin 5) (4 : Fin 5)) (A (1 : Fin 5) (0 : Fin 5)) (A (1 : Fin 5) (1 : Fin 5)) (A (1 : Fin 5) (2 : Fin 5)) (A (1 : Fin 5) (3 : Fin 5)) (A (1 : Fin 5) (4 : Fin 5)) (A (2 : Fin 5) (0 : Fin 5)) (A (2 : Fin 5) (1 : Fin 5)) (A (2 : Fin 5) (2 : Fin 5)) (A (2 : Fin 5) (3 : Fin 5)) (A (2 : Fin 5) (4 : Fin 5)) (A (3 : Fin 5) (0 : Fin 5)) (A (3 : Fin 5) (1 : Fin 5)) (A (3 : Fin 5) (2 : Fin 5)) (A (3 : Fin 5) (3 : Fin 5)) (A (3 : Fin 5) (4 : Fin 5)) (A (4 : Fin 5) (0 : Fin 5)) (A (4 : Fin 5) (1 : Fin 5)) (A (4 : Fin 5) (2 : Fin 5)) (A (4 : Fin 5) (3 : Fin 5)) (A (4 : Fin 5) (4 : Fin 5))

private def frobenius_distance_to_U5_squared_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ) (a15 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ) (a25 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ) (a35 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) (a45 : ℝ)
    (a51 : ℝ) (a52 : ℝ) (a53 : ℝ) (a54 : ℝ) (a55 : ℝ)
    : ℝ :=
  (a11 - 1 / 5) ^ 2 + (a12 - 1 / 5) ^ 2 +
  (a13 - 1 / 5) ^ 2 + (a14 - 1 / 5) ^ 2 + (a15 - 1 / 5) ^ 2 +
  (a21 - 1 / 5) ^ 2 + (a22 - 1 / 5) ^ 2 +
  (a23 - 1 / 5) ^ 2 + (a24 - 1 / 5) ^ 2 + (a25 - 1 / 5) ^ 2 +
  (a31 - 1 / 5) ^ 2 + (a32 - 1 / 5) ^ 2 +
  (a33 - 1 / 5) ^ 2 + (a34 - 1 / 5) ^ 2 + (a35 - 1 / 5) ^ 2 +
  (a41 - 1 / 5) ^ 2 + (a42 - 1 / 5) ^ 2 +
  (a43 - 1 / 5) ^ 2 + (a44 - 1 / 5) ^ 2 + (a45 - 1 / 5) ^ 2 +
  (a51 - 1 / 5) ^ 2 + (a52 - 1 / 5) ^ 2 +
  (a53 - 1 / 5) ^ 2 + (a54 - 1 / 5) ^ 2 + (a55 - 1 / 5) ^ 2

private def frobenius_norm_squared_entries
    (a11 : ℝ) (a12 : ℝ) (a13 : ℝ) (a14 : ℝ) (a15 : ℝ)
    (a21 : ℝ) (a22 : ℝ) (a23 : ℝ) (a24 : ℝ) (a25 : ℝ)
    (a31 : ℝ) (a32 : ℝ) (a33 : ℝ) (a34 : ℝ) (a35 : ℝ)
    (a41 : ℝ) (a42 : ℝ) (a43 : ℝ) (a44 : ℝ) (a45 : ℝ)
    (a51 : ℝ) (a52 : ℝ) (a53 : ℝ) (a54 : ℝ) (a55 : ℝ)
    : ℝ :=
  a11 ^ 2 + a12 ^ 2 + a13 ^ 2 + a14 ^ 2 + a15 ^ 2 +
  a21 ^ 2 + a22 ^ 2 + a23 ^ 2 + a24 ^ 2 + a25 ^ 2 +
  a31 ^ 2 + a32 ^ 2 + a33 ^ 2 + a34 ^ 2 + a35 ^ 2 +
  a41 ^ 2 + a42 ^ 2 + a43 ^ 2 + a44 ^ 2 + a45 ^ 2 +
  a51 ^ 2 + a52 ^ 2 + a53 ^ 2 + a54 ^ 2 + a55 ^ 2

/-- The squared Frobenius norm. Thus `‖A - U5‖_F^2` is `||A - U5||_F^2`. -/
def frobenius_norm_squared (A : Matrix5) : ℝ :=
  frobenius_norm_squared_entries
    (A (0 : Fin 5) (0 : Fin 5)) (A (0 : Fin 5) (1 : Fin 5)) (A (0 : Fin 5) (2 : Fin 5)) (A (0 : Fin 5) (3 : Fin 5)) (A (0 : Fin 5) (4 : Fin 5)) (A (1 : Fin 5) (0 : Fin 5)) (A (1 : Fin 5) (1 : Fin 5)) (A (1 : Fin 5) (2 : Fin 5)) (A (1 : Fin 5) (3 : Fin 5)) (A (1 : Fin 5) (4 : Fin 5)) (A (2 : Fin 5) (0 : Fin 5)) (A (2 : Fin 5) (1 : Fin 5)) (A (2 : Fin 5) (2 : Fin 5)) (A (2 : Fin 5) (3 : Fin 5)) (A (2 : Fin 5) (4 : Fin 5)) (A (3 : Fin 5) (0 : Fin 5)) (A (3 : Fin 5) (1 : Fin 5)) (A (3 : Fin 5) (2 : Fin 5)) (A (3 : Fin 5) (3 : Fin 5)) (A (3 : Fin 5) (4 : Fin 5)) (A (4 : Fin 5) (0 : Fin 5)) (A (4 : Fin 5) (1 : Fin 5)) (A (4 : Fin 5) (2 : Fin 5)) (A (4 : Fin 5) (3 : Fin 5)) (A (4 : Fin 5) (4 : Fin 5))

notation "‖" A "‖_F^2" => frobenius_norm_squared A

abbrev Assignment := DH5GramEvaluation.Assignment

def assignmentOfMatrix (A : Matrix5) : Assignment :=
  fun cell => A cell.1 cell.2

def matrixSum (x : Assignment) : Real :=
  ∑ index : Fin 25, flatAssignment x index

def matrixSquareSum (x : Assignment) : Real :=
  ∑ index : Fin 25, (flatAssignment x index) ^ 2

def uniquenessGapValue (x : Assignment) : Real :=
  matrixSum x ^ 3 *
    ∑ index : Fin 25, (25 * flatAssignment x index - matrixSum x) ^ 2

theorem eval_polySum (x : Fin 25 → Real) (polys : List P) :
    eval x (polySum polys) = (polys.map (eval x)).sum := by
  induction polys with
  | nil => simp [polySum]
  | cons head tail ih => simp [polySum, ih]

theorem eval_allVariables (x : Assignment) :
    eval (flatAssignment x) allVariables = matrixSum x := by
  unfold allVariables
  rw [eval_polySum]
  simp [List.map_map, Function.comp_def]
  unfold matrixSum
  change ((List.range 25).map
    (fun index => flatAssignment x (Fin.ofNat 25 index))).sum =
      ∑ index : Fin 25, flatAssignment x index
  rw [← List.sum_toFinset
    (fun index => flatAssignment x (Fin.ofNat 25 index))
    List.nodup_range]
  simp only [List.toFinset_range]
  rw [← Fin.sum_univ_eq_sum_range
    (fun index => flatAssignment x (Fin.ofNat 25 index)) 25]
  simp

theorem eval_variableSquareSum (x : Assignment) :
    eval (flatAssignment x) variableSquareSum = matrixSquareSum x := by
  unfold variableSquareSum
  rw [eval_polySum]
  simp [List.map_map, Function.comp_def]
  unfold matrixSquareSum
  change ((List.range 25).map
    (fun index => (flatAssignment x (Fin.ofNat 25 index)) ^ 2)).sum =
      ∑ index : Fin 25, (flatAssignment x index) ^ 2
  rw [← List.sum_toFinset
    (fun index => (flatAssignment x (Fin.ofNat 25 index)) ^ 2)
    List.nodup_range]
  simp only [List.toFinset_range]
  rw [← Fin.sum_univ_eq_sum_range
    (fun index => (flatAssignment x (Fin.ofNat 25 index)) ^ 2) 25]
  simp

theorem deviation_square_sum (x : Assignment) :
    (∑ index : Fin 25,
      (25 * flatAssignment x index - matrixSum x) ^ 2) =
        625 * matrixSquareSum x - 25 * matrixSum x ^ 2 := by
  calc
    (∑ index : Fin 25,
      (25 * flatAssignment x index - matrixSum x) ^ 2) =
        ∑ index : Fin 25,
          (625 * (flatAssignment x index) ^ 2 -
            50 * flatAssignment x index * matrixSum x + matrixSum x ^ 2) := by
      apply Finset.sum_congr rfl
      intro index _
      ring
    _ = 625 * matrixSquareSum x -
        50 * matrixSum x * matrixSum x + 25 * matrixSum x ^ 2 := by
      unfold matrixSquareSum matrixSum
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = 625 * matrixSquareSum x - 25 * matrixSum x ^ 2 := by
      ring

theorem eval_uniquenessGapPoly (x : Assignment) :
    eval (flatAssignment x) uniquenessGapPoly = uniquenessGapValue x := by
  rw [show eval (flatAssignment x) uniquenessGapPoly =
      625 * matrixSum x ^ 3 * matrixSquareSum x -
        25 * matrixSum x ^ 5 by
    simp [uniquenessGapPoly, allVariablesPowerFive,
      eval_allVariables, eval_variableSquareSum]
    ring]
  unfold uniquenessGapValue
  rw [deviation_square_sum]
  ring

theorem class_equation (classId : Fin classCount) :
    (classRepetition classId : Int) * classNumerator classId =
      targetCoefficient classId * commonDenominator := by
  rw [classNumerator_eq_computed]
  exact exact_gram_coefficient_equations classId

theorem list_range_foldl_sum {R : Type} [AddCommMonoid R]
    (f : Nat -> R) (n : Nat) :
    (List.range n).foldl (fun total position => total + f position) 0 =
      ∑ position ∈ Finset.range n, f position := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih, Finset.sum_range_succ]

theorem classNumerator_eq_sum (classId : Fin classCount) :
    classNumerator classId =
      ∑ position : Fin 52975, positionNumeratorAt classId position.val := by
  unfold classNumerator
  rw [list_range_foldl_sum]
  rw [← Fin.sum_univ_eq_sum_range (positionNumeratorAt classId) 52975]

def orbitWeight (x : Assignment) (classId : Fin classCount) : Real :=
  ∑ monomial ∈ storedOrbit classId, monomialValue x monomial

theorem orbitWeight_eq_key_sum (x : Assignment) (classId : Fin classCount) :
    orbitWeight x classId =
      ((orbitList classId).map (fun key =>
        monomialValue x (monomialOfKey key))).sum := by
  unfold orbitWeight storedOrbit
  simpa only [List.map_map, Function.comp_def] using
    List.sum_toFinset
      (fun monomial => monomialValue x monomial)
      (orbit_monomial_lists_nodup classId)

theorem eval_orbitClassPoly (x : Assignment) (classId : Fin classCount) :
    SparsePolyCheck.eval (flatAssignment x) (orbitClassPoly classId) =
      (targetCoefficient classId : Real) * orbitWeight x classId := by
  rw [orbitWeight_eq_key_sum]
  unfold orbitClassPoly
  induction orbitList classId with
  | nil => simp [SparsePolyCheck.eval]
  | cons key keys ih =>
      simp only [List.map_cons, SparsePolyCheck.eval_cons, List.sum_cons]
      rw [ih, monomialValue_monomialOfKey]
      unfold orbitTerm SparsePolyCheck.evalTerm
      simp only [Rat.cast_intCast]
      ring

theorem eval_flatten {polys : List P} (x : Fin 25 → Real) :
    SparsePolyCheck.eval x polys.flatten =
      (polys.map (SparsePolyCheck.eval x)).sum := by
  induction polys with
  | nil => simp
  | cons head tail ih =>
      simp [List.flatten, SparsePolyCheck.eval_append, ih]

theorem eval_orbitTargetPoly (x : Assignment) :
    SparsePolyCheck.eval (flatAssignment x) orbitTargetPoly =
      ∑ classId : Fin classCount,
        (targetCoefficient classId : Real) * orbitWeight x classId := by
  unfold orbitTargetPoly
  rw [eval_flatten]
  simp only [List.map_ofFn, Function.comp_def, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro classId _
  exact eval_orbitClassPoly x classId

def totalGram (x : Assignment) : Real :=
  ∑ transformation : Transform, transformedGramTerm x transformation

theorem transformedQuadraticForm_nonnegative (x : Assignment)
    (transformation : Transform) :
    0 ≤ transformedQuadraticForm x transformation := by
  exact fullGramMatrix_posSemidef.dotProduct_mulVec_nonneg
    (transformedBasisValue x transformation)

theorem transformedGramTerm_nonnegative (x : Assignment)
    (entriesNonnegative : ∀ cell, 0 ≤ x cell)
    (transformation : Transform) :
    0 ≤ transformedGramTerm x transformation := by
  unfold transformedGramTerm
  exact mul_nonneg (entriesNonnegative _) (transformedQuadraticForm_nonnegative x transformation)

theorem totalGram_nonnegative (x : Assignment)
    (entriesNonnegative : ∀ cell, 0 ≤ x cell) :
    0 ≤ totalGram x := by
  unfold totalGram
  exact Finset.sum_nonneg fun transformation _ =>
    transformedGramTerm_nonnegative x entriesNonnegative transformation

theorem transformedGramTerm_eq_key_position_sum (x : Assignment)
    (transformation : Transform) :
    transformedGramTerm x transformation =
      ∑ position : Fin 52975,
        positionCoefficient position *
          monomialValue x (actMonomial transformation
            (monomialOfKey (gramMonomialKey position.val))) := by
  rw [transformedGramTerm_eq_position_sum]
  apply Finset.sum_congr rfl
  intro position _
  rw [positionMonomial_eq_keyMonomial]

theorem sum_by_class {R : Type} [CommSemiring R]
    (value : Fin 52975 -> R) (classValue : Fin classCount -> R) :
    (∑ position : Fin 52975,
      value position * classValue (gramClassId position.val)) =
      ∑ classId : Fin classCount,
        (∑ position : Fin 52975,
          if gramClassId position.val = classId then value position else 0) *
          classValue classId := by
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro position _
  rw [Finset.sum_eq_single (gramClassId position.val)]
  · simp
  · intro other _ notEqual
    simp [notEqual.symm]
  · simp

theorem totalGram_eq_class_sum (x : Assignment) :
    totalGram x =
      ∑ classId : Fin classCount,
        (∑ position : Fin 52975,
          if gramClassId position.val = classId then
            positionCoefficient position * (classRepetition classId : Real)
          else 0) * orbitWeight x classId := by
  unfold totalGram
  simp_rw [transformedGramTerm_eq_key_position_sum]
  rw [Finset.sum_comm]
  calc
    (∑ position : Fin 52975, ∑ transformation : Transform,
      positionCoefficient position *
        monomialValue x (actMonomial transformation
          (monomialOfKey (gramMonomialKey position.val)))) =
        ∑ position : Fin 52975,
          (positionCoefficient position *
            (classRepetition (gramClassId position.val) : Real)) *
              orbitWeight x (gramClassId position.val) := by
      apply Finset.sum_congr rfl
      intro position _
      rw [← Finset.mul_sum]
      rw [DH5OrbitSum.gram_entry_transform_sum_compressed position (monomialValue x)]
      simp only [nsmul_eq_mul]
      unfold orbitWeight
      ring
    _ = ∑ classId : Fin classCount,
        (∑ position : Fin 52975,
          if gramClassId position.val = classId then
            positionCoefficient position *
              (classRepetition (gramClassId position.val) : Real)
          else 0) * orbitWeight x classId := sum_by_class
        (fun position => positionCoefficient position *
          (classRepetition (gramClassId position.val) : Real))
        (orbitWeight x)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro classId _
      congr 1
      apply Finset.sum_congr rfl
      intro position _
      by_cases equality : gramClassId position.val = classId
      · simp [equality]
      · simp [equality]

theorem classCoefficient_sum (classId : Fin classCount) :
    (∑ position : Fin 52975,
      if gramClassId position.val = classId then
        positionCoefficient position * (classRepetition classId : Real)
      else 0) = (targetCoefficient classId : Real) := by
  have denominatorPositive : (0 : Real) < (commonDenominator : Real) := by
    exact_mod_cast commonDenominator_pos
  have denominatorNonzero : (commonDenominator : Real) ≠ 0 := denominatorPositive.ne'
  have numeratorCast :
      (classNumerator classId : Real) =
        ∑ position : Fin 52975,
          (positionNumeratorAt classId position.val : Real) := by
    rw [classNumerator_eq_sum]
    norm_cast
  calc
    (∑ position : Fin 52975,
      if gramClassId position.val = classId then
        positionCoefficient position * (classRepetition classId : Real)
      else 0) =
        ((classRepetition classId : Real) * (classNumerator classId : Real)) /
          (commonDenominator : Real) := by
      rw [numeratorCast]
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro position _
      unfold positionCoefficient positionNumeratorAt
      by_cases equality : gramClassId position.val = classId
      · simp [equality]
        ring
      · simp [equality]
    _ = (targetCoefficient classId : Real) := by
      apply (div_eq_iff denominatorNonzero).2
      have exactReal :
          (classRepetition classId : Real) * (classNumerator classId : Real) =
            (targetCoefficient classId : Real) * (commonDenominator : Real) := by
        exact_mod_cast class_equation classId
      exact exactReal

theorem totalGram_eq_orbitTargetPoly (x : Assignment) :
    totalGram x =
      SparsePolyCheck.eval (flatAssignment x) orbitTargetPoly := by
  rw [totalGram_eq_class_sum]
  simp_rw [classCoefficient_sum]
  exact (eval_orbitTargetPoly x).symm

theorem eval_orbitTargetPoly_eq_compactTargetPoly (x : Assignment) :
    SparsePolyCheck.eval (flatAssignment x) orbitTargetPoly =
      SparsePolyCheck.eval (flatAssignment x) compactTargetPoly := by
  have normalized := congrArg (SparsePolyCheck.eval (flatAssignment x))
    orbit_target_is_scaled_margin
  simpa using normalized

theorem eval_compactTargetPoly_nonnegative (x : Assignment)
    (entriesNonnegative : ∀ cell, 0 ≤ x cell) :
    0 ≤ SparsePolyCheck.eval (flatAssignment x) compactTargetPoly := by
  rw [← eval_orbitTargetPoly_eq_compactTargetPoly]
  rw [← totalGram_eq_orbitTargetPoly]
  exact totalGram_nonnegative x entriesNonnegative

theorem eval_compactTargetPoly_formula (x : Assignment) :
    SparsePolyCheck.eval (flatAssignment x) compactTargetPoly =
      100 * SparsePolyCheck.eval (flatAssignment x) h5Poly -
        SparsePolyCheck.eval (flatAssignment x) uniquenessGapPoly := by
  simp [compactTargetPoly]

/-- The exact strengthened DH5 inequality certified by the 325 x 325 Gram matrix. -/
theorem DH5_strengthened (x : Assignment)
    (entriesNonnegative : ∀ cell, 0 ≤ x cell) :
    SparsePolyCheck.eval (flatAssignment x) uniquenessGapPoly / 100 ≤
      SparsePolyCheck.eval (flatAssignment x) h5Poly := by
  have certificateNonnegative :=
    eval_compactTargetPoly_nonnegative x entriesNonnegative
  rw [eval_compactTargetPoly_formula] at certificateNonnegative
  linarith

/-- The strengthened inequality with the uniqueness margin written explicitly. -/
theorem DH5_strengthened_explicit (x : Assignment)
    (entriesNonnegative : ∀ cell, 0 ≤ x cell) :
    uniquenessGapValue x / 100 ≤
      SparsePolyCheck.eval (flatAssignment x) h5Poly := by
  rw [← eval_uniquenessGapPoly]
  exact DH5_strengthened x entriesNonnegative

private theorem eval_polyProduct (x : Fin 25 → Real) (polys : List P) :
    eval x (polyProduct polys) = (polys.map (eval x)).prod := by
  induction polys with
  | nil => simp [polyProduct]
  | cons head tail ih => simp [polyProduct, ih]

private theorem eval_rowSum (A : Matrix5) (row : Fin 5) :
    eval (flatAssignment (assignmentOfMatrix A)) (rowSum row) =
      ∑ column : Fin 5, A row column := by
  unfold rowSum
  rw [eval_polySum]
  simp only [List.map_map, Function.comp_def, SparsePolyCheck.eval_var]
  let value : Nat → Real := fun column =>
    flatAssignment (assignmentOfMatrix A) (Fin.ofNat 25 (5 * row.val + column))
  change ((List.range 5).map value).sum = _
  rw [← List.sum_toFinset value List.nodup_range]
  simp only [List.toFinset_range]
  rw [← Fin.sum_univ_eq_sum_range value 5]
  apply Finset.sum_congr rfl
  intro column _
  unfold value flatAssignment assignmentOfMatrix cellOfIndex
  apply congrArg₂ A
  · apply Fin.ext
    simp only [Fin.ofNat]
    omega
  · apply Fin.ext
    simp only [Fin.ofNat]
    omega

private theorem eval_columnSum (A : Matrix5) (column : Fin 5) :
    eval (flatAssignment (assignmentOfMatrix A)) (columnSum column) =
      ∑ row : Fin 5, A row column := by
  unfold columnSum
  rw [eval_polySum]
  simp only [List.map_map, Function.comp_def, SparsePolyCheck.eval_var]
  let value : Nat → Real := fun row =>
    flatAssignment (assignmentOfMatrix A) (Fin.ofNat 25 (5 * row + column.val))
  change ((List.range 5).map value).sum = _
  rw [← List.sum_toFinset value List.nodup_range]
  simp only [List.toFinset_range]
  rw [← Fin.sum_univ_eq_sum_range value 5]
  apply Finset.sum_congr rfl
  intro row _
  unfold value flatAssignment assignmentOfMatrix cellOfIndex
  apply congrArg₂ A
  · apply Fin.ext
    simp only [Fin.ofNat]
    omega
  · apply Fin.ext
    simp only [Fin.ofNat]
    omega

private theorem eval_rowProduct (A : Matrix5) :
    eval (flatAssignment (assignmentOfMatrix A)) rowProduct =
      ∏ row : Fin 5, ∑ column : Fin 5, A row column := by
  unfold rowProduct
  rw [eval_polyProduct]
  simp only [List.map_ofFn, Function.comp_def, List.prod_ofFn]
  simp_rw [eval_rowSum]

private theorem eval_columnProduct (A : Matrix5) :
    eval (flatAssignment (assignmentOfMatrix A)) columnProduct =
      ∏ column : Fin 5, ∑ row : Fin 5, A row column := by
  unfold columnProduct
  rw [eval_polyProduct]
  simp only [List.map_ofFn, Function.comp_def, List.prod_ofFn]
  simp_rw [eval_columnSum]

private theorem eval_keyMonomial (A : Matrix5) (key : Nat) :
    eval (flatAssignment (assignmentOfMatrix A)) (keyMonomial key) =
      monomialValue (assignmentOfMatrix A) (monomialOfKey key) := by
  rw [monomialValue_monomialOfKey]
  simp [keyMonomial, SparsePolyCheck.monoPoly, SparsePolyCheck.eval,
    SparsePolyCheck.evalTerm]

private theorem monomialValue_key_expanded (A : Matrix5) (key : Nat) :
    monomialValue (assignmentOfMatrix A) (monomialOfKey key) =
      ∏ index : Fin 5, assignmentOfMatrix A (factorsOfKey key index) := by
  unfold monomialOfKey
  exact monomialValue_monomialOfFactors _ _

private def permutationKey (permutation : Equiv.Perm (Fin 5)) : Nat :=
  factorsKey (fun row => (row, permutation.symm row))

private theorem permanent_keys_nodup : permanentKeys.toList.Nodup := by
  native_decide

private theorem permanent_keys_are_permutations :
    permanentKeys.toList.toFinset =
      (Finset.univ : Finset (Equiv.Perm (Fin 5))).image permutationKey := by
  native_decide

private theorem permutationKey_injective : Function.Injective permutationKey := by
  native_decide

private theorem factorsOfKey_permutationKey :
    ∀ permutation : Equiv.Perm (Fin 5),
      factorsOfKey (permutationKey permutation) =
        fun row => (row, permutation.symm row) := by
  native_decide

private theorem eval_permanentPoly (A : Matrix5) :
    eval (flatAssignment (assignmentOfMatrix A)) permanentPoly =
      Matrix.permanent A := by
  unfold permanentPoly
  rw [eval_polySum]
  simp only [List.map_map, Function.comp_def]
  simp_rw [eval_keyMonomial, monomialValue_key_expanded]
  rw [← List.sum_toFinset _ permanent_keys_nodup]
  rw [permanent_keys_are_permutations]
  rw [Matrix.permanent]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro permutation _
    rw [factorsOfKey_permutationKey]
    unfold assignmentOfMatrix
    symm
    exact Fintype.prod_equiv permutation
      (fun column => A (permutation column) column)
      (fun row => A row (permutation.symm row)) (by simp)
  · intro left _ right _ equality
    exact permutationKey_injective equality

private theorem eval_phiPoly (A : Matrix5) :
    eval (flatAssignment (assignmentOfMatrix A)) phiPoly = φ A := by
  simp only [phiPoly, SparsePolyCheck.eval_sub,
    FastPolyForSOS.eval_fastAdd, eval_rowProduct, eval_columnProduct,
    eval_permanentPoly]
  unfold φ φ_entries row_product_entries column_product_entries permanent_entries
  have matrix_entries_eq :
      matrix_entries
        (A 0 0) (A 0 1) (A 0 2) (A 0 3) (A 0 4)
        (A 1 0) (A 1 1) (A 1 2) (A 1 3) (A 1 4)
        (A 2 0) (A 2 1) (A 2 2) (A 2 3) (A 2 4)
        (A 3 0) (A 3 1) (A 3 2) (A 3 3) (A 3 4)
        (A 4 0) (A 4 1) (A 4 2) (A 4 3) (A 4 4) = A := by
    funext row column
    fin_cases row <;> fin_cases column <;> rfl
  rw [matrix_entries_eq]
  let entries : Matrix5 :=
    ![![A 0 0, A 0 1, A 0 2, A 0 3, A 0 4],
      ![A 1 0, A 1 1, A 1 2, A 1 3, A 1 4],
      ![A 2 0, A 2 1, A 2 2, A 2 3, A 2 4],
      ![A 3 0, A 3 1, A 3 2, A 3 3, A 3 4],
      ![A 4 0, A 4 1, A 4 2, A 4 3, A 4 4]]
  have A_eq_entries : A = entries := by
    funext row column
    fin_cases row <;> fin_cases column <;> rfl
  rw [A_eq_entries]
  simp only [Fin.prod_univ_succ, Fin.sum_univ_succ]
  simp
  simp only [add_assoc, mul_assoc]

private theorem frobenius_norm_squared_eq_sum (A : Matrix5) :
    ‖A‖_F^2 = ∑ row : Fin 5, ∑ column : Fin 5, (A row column) ^ 2 := by
  let entries : Matrix5 :=
    ![![A 0 0, A 0 1, A 0 2, A 0 3, A 0 4],
      ![A 1 0, A 1 1, A 1 2, A 1 3, A 1 4],
      ![A 2 0, A 2 1, A 2 2, A 2 3, A 2 4],
      ![A 3 0, A 3 1, A 3 2, A 3 3, A 3 4],
      ![A 4 0, A 4 1, A 4 2, A 4 3, A 4 4]]
  have A_eq_entries : A = entries := by
    funext row column
    fin_cases row <;> fin_cases column <;> rfl
  rw [A_eq_entries]
  unfold frobenius_norm_squared frobenius_norm_squared_entries
  simp only [Fin.sum_univ_succ]
  simp
  ring

private theorem matrixSum_assignmentOfMatrix (A : Matrix5) :
    matrixSum (assignmentOfMatrix A) =
      A 0 0 + A 0 1 + A 0 2 + A 0 3 + A 0 4 +
      A 1 0 + A 1 1 + A 1 2 + A 1 3 + A 1 4 +
      A 2 0 + A 2 1 + A 2 2 + A 2 3 + A 2 4 +
      A 3 0 + A 3 1 + A 3 2 + A 3 3 + A 3 4 +
      A 4 0 + A 4 1 + A 4 2 + A 4 3 + A 4 4 := by
  let entries : Matrix5 :=
    ![![A 0 0, A 0 1, A 0 2, A 0 3, A 0 4],
      ![A 1 0, A 1 1, A 1 2, A 1 3, A 1 4],
      ![A 2 0, A 2 1, A 2 2, A 2 3, A 2 4],
      ![A 3 0, A 3 1, A 3 2, A 3 3, A 3 4],
      ![A 4 0, A 4 1, A 4 2, A 4 3, A 4 4]]
  have A_eq_entries : A = entries := by
    funext row column
    fin_cases row <;> fin_cases column <;> rfl
  rw [A_eq_entries]
  unfold matrixSum
  simp only [Fin.sum_univ_succ]
  norm_num [flatAssignment, assignmentOfMatrix, cellOfIndex, Fin.ofNat, entries,
    Matrix.cons_val]
  simp
  ring

private theorem eval_h5Poly (A : Matrix5) :
    eval (flatAssignment (assignmentOfMatrix A)) h5Poly =
      1226 * matrixSum (assignmentOfMatrix A) ^ 5 - 1953125 * φ A := by
  simp [h5Poly, allVariablesPowerFive, eval_allVariables, eval_phiPoly]

private theorem uniquenessGapValue_on_sum_five (A : Matrix5)
    (hsum : matrixSum (assignmentOfMatrix A) = 5) :
    uniquenessGapValue (assignmentOfMatrix A) =
      78125 * ‖A - U5‖_F^2 := by
  let entries : Matrix5 :=
    ![![A 0 0, A 0 1, A 0 2, A 0 3, A 0 4],
      ![A 1 0, A 1 1, A 1 2, A 1 3, A 1 4],
      ![A 2 0, A 2 1, A 2 2, A 2 3, A 2 4],
      ![A 3 0, A 3 1, A 3 2, A 3 3, A 3 4],
      ![A 4 0, A 4 1, A 4 2, A 4 3, A 4 4]]
  have A_eq_entries : A = entries := by
    funext row column
    fin_cases row <;> fin_cases column <;> rfl
  rw [A_eq_entries] at hsum ⊢
  unfold uniquenessGapValue
  rw [hsum]
  unfold frobenius_norm_squared frobenius_norm_squared_entries U5
  simp only [Fin.sum_univ_succ]
  norm_num [flatAssignment, assignmentOfMatrix, cellOfIndex, Fin.ofNat, entries,
    Matrix.sub_apply]
  simp
  ring

private theorem phi_U5_eq :
    φ U5 = 1226 / 625 := by
  unfold φ φ_entries row_product_entries column_product_entries U5
  unfold permanent_entries
  rw [show matrix_entries
      (1 / 5) (1 / 5) (1 / 5) (1 / 5) (1 / 5)
      (1 / 5) (1 / 5) (1 / 5) (1 / 5) (1 / 5)
      (1 / 5) (1 / 5) (1 / 5) (1 / 5) (1 / 5)
      (1 / 5) (1 / 5) (1 / 5) (1 / 5) (1 / 5)
      (1 / 5) (1 / 5) (1 / 5) (1 / 5) (1 / 5) = U5 by
    funext row column
    fin_cases row <;> fin_cases column <;> rfl]
  norm_num [Matrix.permanent, U5, Fintype.card_perm]

private theorem frobenius_norm_squared_nonneg (A : Matrix5) :
    0 ≤ ‖A‖_F^2 := by
  unfold frobenius_norm_squared frobenius_norm_squared_entries
  positivity

private theorem frobenius_norm_squared_sub_U5_eq_zero_iff (A : Matrix5) :
    ‖A - U5‖_F^2 = 0 ↔ A = U5 := by
  constructor
  · intro hdist
    have hsum :
        (∑ row : Fin 5, ∑ column : Fin 5,
          ((A - U5) row column) ^ 2) = 0 := by
      rw [← frobenius_norm_squared_eq_sum]
      exact hdist
    have hrow : ∀ row : Fin 5,
        (∑ column : Fin 5, ((A - U5) row column) ^ 2) = 0 := by
      have hrow_fun := (Fintype.sum_eq_zero_iff_of_nonneg
        (fun row => Finset.sum_nonneg
          (fun column _ => sq_nonneg ((A - U5) row column)))).mp hsum
      intro row
      exact congrFun hrow_fun row
    have hentry : ∀ row column : Fin 5,
        ((A - U5) row column) ^ 2 = 0 := by
      intro row
      have hentry_fun := (Fintype.sum_eq_zero_iff_of_nonneg
        (fun column => sq_nonneg ((A - U5) row column))).mp (hrow row)
      intro column
      exact congrFun hentry_fun column
    funext row column
    have hsquare := hentry row column
    change (A row column - (1 / 5 : ℝ)) ^ 2 = 0 at hsquare
    change A row column = (1 / 5 : ℝ)
    nlinarith
  · intro hA
    subst A
    unfold frobenius_norm_squared frobenius_norm_squared_entries U5
    norm_num

/--
Theorem 1.2, informal statement.

This is the quantitative stability estimate used to prove the Dittert
conjecture in dimension 5.

Here `K5` is the simplex of all `5 × 5` real matrices with nonnegative entries
and total sum equal to `5`. The matrix `U5` is the uniform matrix whose twenty-
five entries are all `1 / 5`. The function `φ` is the Dittert functional:
the product of the five row sums, plus the product of the five column sums,
minus the permanent.

The theorem says that every matrix `A` in `K5` satisfies a stronger estimate
than just `φ A ≤ 1226 / 625`: the gap from the optimal value controls the
squared Frobenius distance from `A` to the uniform matrix `U5`.
-/

theorem theorem_1_2_quantitative_stability_for_DH5
    (A : Matrix5) (hA : A ∈ K5) :
    (1226 / 625 : ℝ) - φ A ≥ (1 / 2500 : ℝ) * ‖A - U5‖_F^2 := by
  rcases hA with ⟨h_nonneg, hsum⟩
  have hsum_assignment : matrixSum (assignmentOfMatrix A) = 5 := by
    rw [matrixSum_assignmentOfMatrix]
    exact hsum
  have htarget := DH5_strengthened_explicit (assignmentOfMatrix A)
    (fun cell => h_nonneg cell.1 cell.2)
  rw [eval_h5Poly, uniquenessGapValue_on_sum_five A hsum_assignment,
    hsum_assignment] at htarget
  linarith

/--
Theorem 1.1, informal statement.

This is the Dittert conjecture in dimension 5, together with the uniqueness of
the equality case. The theorem proves that `1226 / 625` is the global maximum
of `φ` on `K5`, and that equality holds exactly at the uniform matrix `U5`.
-/

theorem theorem_1_1_dittert_conjecture_dimension_five
    (A : Matrix5) (hA : A ∈ K5) :
    φ A ≤ 1226 / 625 ∧ (φ A = 1226 / 625 ↔ A = U5) := by
  constructor
  · have hstable := theorem_1_2_quantitative_stability_for_DH5
      A hA
    have hdist_nonneg := frobenius_norm_squared_nonneg (A - U5)
    linarith
  · constructor
    · intro hphi
      have hstable := theorem_1_2_quantitative_stability_for_DH5
        A hA
      have hdist_nonneg := frobenius_norm_squared_nonneg (A - U5)
      have hdist_zero : ‖A - U5‖_F^2 = 0 := by
        linarith
      exact (frobenius_norm_squared_sub_U5_eq_zero_iff A).mp hdist_zero
    · intro hAeq
      subst A
      exact phi_U5_eq

end DH5Main
