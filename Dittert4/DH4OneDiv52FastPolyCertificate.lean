import Dittert4.DH4OneDiv52FastPolyData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section

namespace DH4OneDiv52FastPolyCertificate

open SparsePolyCheck DH4OneDiv52FastPolyData

abbrev P := Poly 16
abbrev Squares := List (ℚ × P)

def sos : Squares → P
  | [] => []
  | (weight, form) :: rest =>
      add (scale weight (square form)) (sos rest)

def permutePoly (inverse : List Nat) (poly : P) : P :=
  poly.map fun item =>
    { item with exp := fun index => item.exp (Fin.ofNat 16 (inverse.getD index.val 0)) }

def permuteSquares (inverse : List Nat) (squares : Squares) : Squares :=
  squares.map fun (weight, form) => (weight, permutePoly inverse form)

def generator : List Nat → P
  | [] => const 1
  | index :: rest => mul (var (Fin.ofNat 16 index)) (generator rest)

def assignmentCertificate (assignment : Assignment) : P :=
  let squares := templates.getD assignment.template []
  let inverse := inverseTransforms.getD assignment.transform []
  mul (generator assignment.generator) (sos (permuteSquares inverse squares))

def assignmentSum : List Assignment → P
  | [] => []
  | assignment :: rest => add (assignmentCertificate assignment) (assignmentSum rest)

def positiveCertificate : P :=
  add (sos mainSquares) (assignmentSum assignments)

def polySum : List P → P
  | [] => []
  | poly :: rest => add poly (polySum rest)

def polyProduct : List P → P
  | [] => const 1
  | poly :: rest => mul poly (polyProduct rest)

@[simp] theorem eval_polySum (x : Fin 16 → ℝ) (polys : List P) :
    eval x (polySum polys) = (polys.map (eval x)).sum := by
  induction polys with
  | nil => simp [polySum]
  | cons poly rest inductionHypothesis =>
      simp [polySum, inductionHypothesis]

def simplexEquality : P :=
  sub (polySum [var 0, var 1, var 2, var 3, var 4, var 5, var 6, var 7, var 8, var 9, var 10, var 11, var 12, var 13, var 14, var 15]) (const 4)

def row0 : P :=
  polySum [var 0, var 1, var 2, var 3]

def row1 : P :=
  polySum [var 4, var 5, var 6, var 7]

def row2 : P :=
  polySum [var 8, var 9, var 10, var 11]

def row3 : P :=
  polySum [var 12, var 13, var 14, var 15]

def column0 : P :=
  polySum [var 0, var 4, var 8, var 12]

def column1 : P :=
  polySum [var 1, var 5, var 9, var 13]

def column2 : P :=
  polySum [var 2, var 6, var 10, var 14]

def column3 : P :=
  polySum [var 3, var 7, var 11, var 15]

def rowProductPoly : P :=
  polyProduct [row0, row1, row2, row3]

def columnProductPoly : P :=
  polyProduct [column0, column1, column2, column3]

def permanentPoly : P :=
  polySum [
    generator [0, 5, 10, 15],
    generator [0, 5, 11, 14],
    generator [0, 6, 9, 15],
    generator [0, 6, 11, 13],
    generator [0, 7, 9, 14],
    generator [0, 7, 10, 13],
    generator [1, 4, 10, 15],
    generator [1, 4, 11, 14],
    generator [1, 6, 8, 15],
    generator [1, 6, 11, 12],
    generator [1, 7, 8, 14],
    generator [1, 7, 10, 12],
    generator [2, 4, 9, 15],
    generator [2, 4, 11, 13],
    generator [2, 5, 8, 15],
    generator [2, 5, 11, 12],
    generator [2, 7, 8, 13],
    generator [2, 7, 9, 12],
    generator [3, 4, 9, 14],
    generator [3, 4, 10, 13],
    generator [3, 5, 8, 14],
    generator [3, 5, 10, 12],
    generator [3, 6, 8, 13],
    generator [3, 6, 9, 12]
  ]

def dh4IntegerPoly : P :=
  polySum [const 61, scale (-32) rowProductPoly, scale (-32) columnProductPoly,
    scale 32 permanentPoly]

def centeredSquare (index : Nat) : P :=
  square (sub (var (Fin.ofNat 16 index)) (const (1 / 4)))

def d4Poly : P :=
  polySum [
    centeredSquare 0,
    centeredSquare 1,
    centeredSquare 2,
    centeredSquare 3,
    centeredSquare 4,
    centeredSquare 5,
    centeredSquare 6,
    centeredSquare 7,
    centeredSquare 8,
    centeredSquare 9,
    centeredSquare 10,
    centeredSquare 11,
    centeredSquare 12,
    centeredSquare 13,
    centeredSquare 14,
    centeredSquare 15
  ]

def compactTarget : P :=
  sub (scale 13 dh4IntegerPoly) (scale 8 d4Poly)

def rawCertificate : P :=
  add positiveCertificate (mul simplexEquality qPoly)

def WeightsNonnegative (squares : Squares) : Prop :=
  ∀ item ∈ squares, 0 ≤ item.1

def weightsNonnegativeBool (squares : Squares) : Bool :=
  squares.all fun item => decide (0 ≤ item.1)

theorem weightsNonnegative_of_bool (squares : Squares)
    (result : weightsNonnegativeBool squares = true) :
    WeightsNonnegative squares := by
  intro item itemInSquares
  have allResult : ∀ source ∈ squares, decide (0 ≤ source.1) = true := by
    simpa [weightsNonnegativeBool, List.all_eq_true] using result
  exact of_decide_eq_true (allResult item itemInSquares)

theorem eval_sos_nonneg (x : Fin 16 → ℝ) (squares : Squares)
    (weightsNonnegative : WeightsNonnegative squares) :
    0 ≤ eval x (sos squares) := by
  induction squares with
  | nil => simp [sos]
  | cons item rest inductionHypothesis =>
      rcases item with ⟨weight, form⟩
      rw [sos, eval_add, eval_scale, eval_square]
      apply add_nonneg
      · exact mul_nonneg
          (Rat.cast_nonneg.mpr
            (weightsNonnegative (weight, form) (by simp)))
          (sq_nonneg _)
      · apply inductionHypothesis
        intro item itemInRest
        exact weightsNonnegative item (by simp [itemInRest])

theorem weightsNonnegative_permute (inverse : List Nat) (squares : Squares)
    (weightsNonnegative : WeightsNonnegative squares) :
    WeightsNonnegative (permuteSquares inverse squares) := by
  intro item itemInPermuted
  simp only [permuteSquares, List.mem_map] at itemInPermuted
  obtain ⟨source, sourceInSquares, sourceImage⟩ := itemInPermuted
  rcases source with ⟨weight, form⟩
  simp only at sourceImage
  subst item
  exact weightsNonnegative (weight, form) sourceInSquares

theorem eval_generator_nonneg (x : Fin 16 → ℝ)
    (variablesNonnegative : ∀ index, 0 ≤ x index) (indices : List Nat) :
    0 ≤ eval x (generator indices) := by
  induction indices with
  | nil => simp [generator]
  | cons index rest inductionHypothesis =>
      rw [generator, eval_mul, eval_var]
      exact mul_nonneg (variablesNonnegative _) inductionHypothesis

theorem eval_assignmentCertificate_nonneg (x : Fin 16 → ℝ)
    (variablesNonnegative : ∀ index, 0 ≤ x index) (assignment : Assignment)
    (templateWeightsNonnegative :
      WeightsNonnegative (templates.getD assignment.template [])) :
    0 ≤ eval x (assignmentCertificate assignment) := by
  rw [assignmentCertificate, eval_mul]
  exact mul_nonneg
    (eval_generator_nonneg x variablesNonnegative assignment.generator)
    (eval_sos_nonneg x _
      (weightsNonnegative_permute _ _ templateWeightsNonnegative))

theorem eval_assignmentSum_nonneg (x : Fin 16 → ℝ)
    (variablesNonnegative : ∀ index, 0 ≤ x index) (items : List Assignment)
    (templateWeightsNonnegative : ∀ assignment ∈ items,
      WeightsNonnegative (templates.getD assignment.template [])) :
    0 ≤ eval x (assignmentSum items) := by
  induction items with
  | nil => simp [assignmentSum]
  | cons assignment rest inductionHypothesis =>
      rw [assignmentSum, eval_add]
      apply add_nonneg
      · exact eval_assignmentCertificate_nonneg x variablesNonnegative assignment
          (templateWeightsNonnegative assignment (by simp))
      · apply inductionHypothesis
        intro item itemInRest
        exact templateWeightsNonnegative item (by simp [itemInRest])

theorem main_weights_nonnegative : WeightsNonnegative mainSquares := by
  apply weightsNonnegative_of_bool
  native_decide

def assignmentTemplatesWeightsNonnegativeBool : Bool :=
  assignments.all fun assignment =>
    weightsNonnegativeBool (templates.getD assignment.template [])

theorem assignment_templates_weights_nonnegative :
    ∀ assignment ∈ assignments,
      WeightsNonnegative (templates.getD assignment.template []) := by
  intro assignment assignmentInAssignments
  apply weightsNonnegative_of_bool
  have allResult :
      ∀ source ∈ assignments,
        weightsNonnegativeBool (templates.getD source.template []) = true := by
    simpa [assignmentTemplatesWeightsNonnegativeBool, List.all_eq_true] using
      (show assignmentTemplatesWeightsNonnegativeBool = true by native_decide)
  exact allResult assignment assignmentInAssignments

theorem eval_positiveCertificate_nonneg (x : Fin 16 → ℝ)
    (variablesNonnegative : ∀ index, 0 ≤ x index) :
    0 ≤ eval x positiveCertificate := by
  rw [positiveCertificate, eval_add]
  exact add_nonneg
    (eval_sos_nonneg x mainSquares main_weights_nonnegative)
    (eval_assignmentSum_nonneg x variablesNonnegative assignments
      assignment_templates_weights_nonnegative)

theorem normalized_certificate :
    FastPolyForSOS.fastNormalize rawCertificate = targetPoly := by
  native_decide

theorem normalized_compactTarget :
    FastPolyForSOS.fastNormalize compactTarget = targetPoly := by
  native_decide

theorem eval_rawCertificate_nonneg (x : Fin 16 → ℝ)
    (variablesNonnegative : ∀ index, 0 ≤ x index)
    (simplexZero : eval x simplexEquality = 0) :
    0 ≤ eval x rawCertificate := by
  rw [rawCertificate, eval_add, eval_mul, simplexZero, zero_mul, add_zero]
  exact eval_positiveCertificate_nonneg x variablesNonnegative

theorem eval_targetPoly_nonneg (x : Fin 16 → ℝ)
    (variablesNonnegative : ∀ index, 0 ≤ x index)
    (simplexZero : eval x simplexEquality = 0) :
    0 ≤ eval x targetPoly := by
  have normalizedEvaluation := congrArg (eval x) normalized_certificate
  rw [FastPolyForSOS.eval_fastNormalize] at normalizedEvaluation
  rw [← normalizedEvaluation]
  exact eval_rawCertificate_nonneg x variablesNonnegative simplexZero

def point
    (x1 : ℝ) (x2 : ℝ) (x3 : ℝ) (x4 : ℝ)
    (x5 : ℝ) (x6 : ℝ) (x7 : ℝ) (x8 : ℝ)
    (x9 : ℝ) (x10 : ℝ) (x11 : ℝ) (x12 : ℝ)
    (x13 : ℝ) (x14 : ℝ) (x15 : ℝ) (x16 : ℝ) (i : Fin 16) : ℝ :=
  match i.val with
  | 0 => x1
  | 1 => x2
  | 2 => x3
  | 3 => x4
  | 4 => x5
  | 5 => x6
  | 6 => x7
  | 7 => x8
  | 8 => x9
  | 9 => x10
  | 10 => x11
  | 11 => x12
  | 12 => x13
  | 13 => x14
  | 14 => x15
  | _ => x16

def DH4
    (x1 : ℝ) (x2 : ℝ) (x3 : ℝ) (x4 : ℝ)
    (x5 : ℝ) (x6 : ℝ) (x7 : ℝ) (x8 : ℝ)
    (x9 : ℝ) (x10 : ℝ) (x11 : ℝ) (x12 : ℝ)
    (x13 : ℝ) (x14 : ℝ) (x15 : ℝ) (x16 : ℝ) : ℝ :=
  eval (point x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) dh4IntegerPoly / 32

def D4
    (x1 : ℝ) (x2 : ℝ) (x3 : ℝ) (x4 : ℝ)
    (x5 : ℝ) (x6 : ℝ) (x7 : ℝ) (x8 : ℝ)
    (x9 : ℝ) (x10 : ℝ) (x11 : ℝ) (x12 : ℝ)
    (x13 : ℝ) (x14 : ℝ) (x15 : ℝ) (x16 : ℝ) : ℝ :=
  eval (point x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) d4Poly

def D4Entries
    (x1 : ℝ) (x2 : ℝ) (x3 : ℝ) (x4 : ℝ)
    (x5 : ℝ) (x6 : ℝ) (x7 : ℝ) (x8 : ℝ)
    (x9 : ℝ) (x10 : ℝ) (x11 : ℝ) (x12 : ℝ)
    (x13 : ℝ) (x14 : ℝ) (x15 : ℝ) (x16 : ℝ) : ℝ :=
  (x1 - 1 / 4) ^ 2
  + (x2 - 1 / 4) ^ 2
  + (x3 - 1 / 4) ^ 2
  + (x4 - 1 / 4) ^ 2
  + (x5 - 1 / 4) ^ 2
  + (x6 - 1 / 4) ^ 2
  + (x7 - 1 / 4) ^ 2
  + (x8 - 1 / 4) ^ 2
  + (x9 - 1 / 4) ^ 2
  + (x10 - 1 / 4) ^ 2
  + (x11 - 1 / 4) ^ 2
  + (x12 - 1 / 4) ^ 2
  + (x13 - 1 / 4) ^ 2
  + (x14 - 1 / 4) ^ 2
  + (x15 - 1 / 4) ^ 2
  + (x16 - 1 / 4) ^ 2

theorem D4_eq_D4Entries
    (x1 : ℝ) (x2 : ℝ) (x3 : ℝ) (x4 : ℝ)
    (x5 : ℝ) (x6 : ℝ) (x7 : ℝ) (x8 : ℝ)
    (x9 : ℝ) (x10 : ℝ) (x11 : ℝ) (x12 : ℝ)
    (x13 : ℝ) (x14 : ℝ) (x15 : ℝ) (x16 : ℝ) :
    D4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 =
      D4Entries x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 := by
  norm_num [D4, D4Entries, d4Poly, centeredSquare, polySum, point]
  ring_nf

theorem D4Entries_eq_zero_iff
    (x1 : ℝ) (x2 : ℝ) (x3 : ℝ) (x4 : ℝ)
    (x5 : ℝ) (x6 : ℝ) (x7 : ℝ) (x8 : ℝ)
    (x9 : ℝ) (x10 : ℝ) (x11 : ℝ) (x12 : ℝ)
    (x13 : ℝ) (x14 : ℝ) (x15 : ℝ) (x16 : ℝ) :
    D4Entries x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 = 0 ↔
      x1 = 1 / 4 ∧ x2 = 1 / 4 ∧ x3 = 1 / 4 ∧ x4 = 1 / 4 ∧
      x5 = 1 / 4 ∧ x6 = 1 / 4 ∧ x7 = 1 / 4 ∧ x8 = 1 / 4 ∧
      x9 = 1 / 4 ∧ x10 = 1 / 4 ∧ x11 = 1 / 4 ∧ x12 = 1 / 4 ∧
      x13 = 1 / 4 ∧ x14 = 1 / 4 ∧ x15 = 1 / 4 ∧ x16 = 1 / 4 := by
  constructor
  · intro h
    unfold D4Entries at h
    have h1_nonneg : 0 ≤ (x1 - 1 / 4) ^ 2 := sq_nonneg _
    have h2_nonneg : 0 ≤ (x2 - 1 / 4) ^ 2 := sq_nonneg _
    have h3_nonneg : 0 ≤ (x3 - 1 / 4) ^ 2 := sq_nonneg _
    have h4_nonneg : 0 ≤ (x4 - 1 / 4) ^ 2 := sq_nonneg _
    have h5_nonneg : 0 ≤ (x5 - 1 / 4) ^ 2 := sq_nonneg _
    have h6_nonneg : 0 ≤ (x6 - 1 / 4) ^ 2 := sq_nonneg _
    have h7_nonneg : 0 ≤ (x7 - 1 / 4) ^ 2 := sq_nonneg _
    have h8_nonneg : 0 ≤ (x8 - 1 / 4) ^ 2 := sq_nonneg _
    have h9_nonneg : 0 ≤ (x9 - 1 / 4) ^ 2 := sq_nonneg _
    have h10_nonneg : 0 ≤ (x10 - 1 / 4) ^ 2 := sq_nonneg _
    have h11_nonneg : 0 ≤ (x11 - 1 / 4) ^ 2 := sq_nonneg _
    have h12_nonneg : 0 ≤ (x12 - 1 / 4) ^ 2 := sq_nonneg _
    have h13_nonneg : 0 ≤ (x13 - 1 / 4) ^ 2 := sq_nonneg _
    have h14_nonneg : 0 ≤ (x14 - 1 / 4) ^ 2 := sq_nonneg _
    have h15_nonneg : 0 ≤ (x15 - 1 / 4) ^ 2 := sq_nonneg _
    have h16_nonneg : 0 ≤ (x16 - 1 / 4) ^ 2 := sq_nonneg _
    have hx1_sq : (x1 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx2_sq : (x2 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx3_sq : (x3 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx4_sq : (x4 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx5_sq : (x5 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx6_sq : (x6 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx7_sq : (x7 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx8_sq : (x8 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx9_sq : (x9 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx10_sq : (x10 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx11_sq : (x11 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx12_sq : (x12 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx13_sq : (x13 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx14_sq : (x14 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx15_sq : (x15 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx16_sq : (x16 - 1 / 4) ^ 2 = 0 := by nlinarith
    have hx1 : x1 = 1 / 4 := by
      have hlin : x1 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx1_sq
      linarith
    have hx2 : x2 = 1 / 4 := by
      have hlin : x2 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx2_sq
      linarith
    have hx3 : x3 = 1 / 4 := by
      have hlin : x3 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx3_sq
      linarith
    have hx4 : x4 = 1 / 4 := by
      have hlin : x4 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx4_sq
      linarith
    have hx5 : x5 = 1 / 4 := by
      have hlin : x5 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx5_sq
      linarith
    have hx6 : x6 = 1 / 4 := by
      have hlin : x6 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx6_sq
      linarith
    have hx7 : x7 = 1 / 4 := by
      have hlin : x7 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx7_sq
      linarith
    have hx8 : x8 = 1 / 4 := by
      have hlin : x8 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx8_sq
      linarith
    have hx9 : x9 = 1 / 4 := by
      have hlin : x9 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx9_sq
      linarith
    have hx10 : x10 = 1 / 4 := by
      have hlin : x10 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx10_sq
      linarith
    have hx11 : x11 = 1 / 4 := by
      have hlin : x11 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx11_sq
      linarith
    have hx12 : x12 = 1 / 4 := by
      have hlin : x12 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx12_sq
      linarith
    have hx13 : x13 = 1 / 4 := by
      have hlin : x13 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx13_sq
      linarith
    have hx14 : x14 = 1 / 4 := by
      have hlin : x14 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx14_sq
      linarith
    have hx15 : x15 = 1 / 4 := by
      have hlin : x15 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx15_sq
      linarith
    have hx16 : x16 = 1 / 4 := by
      have hlin : x16 - 1 / 4 = 0 := sq_eq_zero_iff.mp hx16_sq
      linarith
    exact ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16⟩
  · intro h
    rcases h with ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16⟩
    unfold D4Entries
    norm_num [hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8,
      hx9, hx10, hx11, hx12, hx13, hx14, hx15, hx16]

theorem D4_eq_zero_iff
    (x1 : ℝ) (x2 : ℝ) (x3 : ℝ) (x4 : ℝ)
    (x5 : ℝ) (x6 : ℝ) (x7 : ℝ) (x8 : ℝ)
    (x9 : ℝ) (x10 : ℝ) (x11 : ℝ) (x12 : ℝ)
    (x13 : ℝ) (x14 : ℝ) (x15 : ℝ) (x16 : ℝ) :
    D4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 = 0 ↔
      x1 = 1 / 4 ∧ x2 = 1 / 4 ∧ x3 = 1 / 4 ∧ x4 = 1 / 4 ∧
      x5 = 1 / 4 ∧ x6 = 1 / 4 ∧ x7 = 1 / 4 ∧ x8 = 1 / 4 ∧
      x9 = 1 / 4 ∧ x10 = 1 / 4 ∧ x11 = 1 / 4 ∧ x12 = 1 / 4 ∧
      x13 = 1 / 4 ∧ x14 = 1 / 4 ∧ x15 = 1 / 4 ∧ x16 = 1 / 4 := by
  rw [D4_eq_D4Entries]
  exact D4Entries_eq_zero_iff x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16

theorem eval_simplexEquality_point
    (x1 : ℝ) (x2 : ℝ) (x3 : ℝ) (x4 : ℝ)
    (x5 : ℝ) (x6 : ℝ) (x7 : ℝ) (x8 : ℝ)
    (x9 : ℝ) (x10 : ℝ) (x11 : ℝ) (x12 : ℝ)
    (x13 : ℝ) (x14 : ℝ) (x15 : ℝ) (x16 : ℝ) :
    eval (point x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) simplexEquality =
      x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 - 4 := by
  norm_num [simplexEquality, polySum, point]
  ring_nf

theorem eval_compactTarget_point
    (x1 : ℝ) (x2 : ℝ) (x3 : ℝ) (x4 : ℝ)
    (x5 : ℝ) (x6 : ℝ) (x7 : ℝ) (x8 : ℝ)
    (x9 : ℝ) (x10 : ℝ) (x11 : ℝ) (x12 : ℝ)
    (x13 : ℝ) (x14 : ℝ) (x15 : ℝ) (x16 : ℝ) :
    eval (point x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) compactTarget =
      416 * DH4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 - 8 * D4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 := by
  simp [compactTarget, DH4, D4]
  ring

theorem DH4_one_div_52_scaled_sos
    (x1 : ℝ) (x2 : ℝ) (x3 : ℝ) (x4 : ℝ)
    (x5 : ℝ) (x6 : ℝ) (x7 : ℝ) (x8 : ℝ)
    (x9 : ℝ) (x10 : ℝ) (x11 : ℝ) (x12 : ℝ)
    (x13 : ℝ) (x14 : ℝ) (x15 : ℝ) (x16 : ℝ)
    (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3) (h4 : 0 ≤ x4)
    (h5 : 0 ≤ x5) (h6 : 0 ≤ x6) (h7 : 0 ≤ x7) (h8 : 0 ≤ x8)
    (h9 : 0 ≤ x9) (h10 : 0 ≤ x10) (h11 : 0 ≤ x11) (h12 : 0 ≤ x12)
    (h13 : 0 ≤ x13) (h14 : 0 ≤ x14) (h15 : 0 ≤ x15) (h16 : 0 ≤ x16)
    (hsum : x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 = 4) :
    0 ≤ 416 * DH4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 - 8 * D4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 := by
  let x := point x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
  have variablesNonnegative : ∀ index, 0 ≤ x index := by
    intro index
    fin_cases index <;>
      simp [x, point, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16]
  have simplexZero : eval x simplexEquality = 0 := by
    rw [show x = point x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 by rfl, eval_simplexEquality_point]
    linarith
  have targetNonnegative := eval_targetPoly_nonneg x variablesNonnegative simplexZero
  have compactEvaluation := congrArg (eval x) normalized_compactTarget
  rw [FastPolyForSOS.eval_fastNormalize] at compactEvaluation
  have compactNonnegative : 0 ≤ eval x compactTarget := by
    rw [compactEvaluation]
    exact targetNonnegative
  rw [show x = point x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 by rfl, eval_compactTarget_point] at compactNonnegative
  exact compactNonnegative

theorem DH4_one_div_52_sos
    (x1 : ℝ) (x2 : ℝ) (x3 : ℝ) (x4 : ℝ)
    (x5 : ℝ) (x6 : ℝ) (x7 : ℝ) (x8 : ℝ)
    (x9 : ℝ) (x10 : ℝ) (x11 : ℝ) (x12 : ℝ)
    (x13 : ℝ) (x14 : ℝ) (x15 : ℝ) (x16 : ℝ)
    (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3) (h4 : 0 ≤ x4)
    (h5 : 0 ≤ x5) (h6 : 0 ≤ x6) (h7 : 0 ≤ x7) (h8 : 0 ≤ x8)
    (h9 : 0 ≤ x9) (h10 : 0 ≤ x10) (h11 : 0 ≤ x11) (h12 : 0 ≤ x12)
    (h13 : 0 ≤ x13) (h14 : 0 ≤ x14) (h15 : 0 ≤ x15) (h16 : 0 ≤ x16)
    (hsum : x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 = 4) :
    0 ≤ DH4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 - (1 / 52 : ℝ) * D4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 := by
  have hscaled := DH4_one_div_52_scaled_sos x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 hsum
  have hrewrite :
      416 * (DH4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 - (1 / 52 : ℝ) * D4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) =
        416 * DH4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 - 8 * D4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 := by
    ring
  rw [← hrewrite] at hscaled
  have hscaled' :
      0 ≤
        (DH4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 - (1 / 52 : ℝ) * D4 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) * 416 := by
    simpa [mul_comm] using hscaled
  exact nonneg_of_mul_nonneg_left hscaled' (by norm_num : (0 : ℝ) < 416)

end DH4OneDiv52FastPolyCertificate
