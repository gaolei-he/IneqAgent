import Dittert5.DH5GramLiftAudit

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace DH5PSD

open scoped BigOperators
open DH5GramData DH5PSDAudit DH5GramLiftAudit Matrix

/-- A real symmetric matrix whose diagonal dominates each row is positive semidefinite. -/
theorem posSemidef_of_symmetric_diagonal_dominant
    {n : Type} [Fintype n] [DecidableEq n]
    (matrix : Matrix n n ℝ)
    (symmetric : matrix.IsHermitian)
    (dominant : ∀ row, ∑ column, (if column = row then 0 else |matrix row column|) ≤
      matrix row row) :
    matrix.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg symmetric
  intro values
  let weight : n → n → ℝ := fun row column =>
    if column = row then 0 else |matrix row column|
  let offDiagonal : n → n → ℝ := fun row column =>
    if column = row then 0 else matrix row column
  let weightedDiagonal : ℝ :=
    ∑ row, (∑ column, weight row column) * values row ^ 2
  let diagonalPart : ℝ :=
    ∑ row, matrix row row * values row ^ 2
  let offDiagonalPart : ℝ :=
    ∑ row, ∑ column, offDiagonal row column * values row * values column

  have weight_symmetric (row column : n) : weight row column = weight column row := by
    by_cases equality : column = row
    · subst column
      simp [weight]
    · have reverseEquality : row ≠ column := Ne.symm equality
      have entryEquality : matrix row column = matrix column row := by
        have := congrFun (congrFun symmetric row) column
        simpa [Matrix.conjTranspose_apply] using this.symm
      simp [weight, equality, reverseEquality, entryEquality]

  have pair_bound (row column : n) :
      -(weight row column * (values row ^ 2 + values column ^ 2)) ≤
        2 * offDiagonal row column * values row * values column := by
    by_cases equality : column = row
    · simp [weight, offDiagonal, equality]
    · simp only [weight, offDiagonal, equality, ↓reduceIte]
      by_cases entryNonnegative : 0 ≤ matrix row column
      · rw [abs_of_nonneg entryNonnegative]
        have squareNonnegative : 0 ≤ matrix row column *
            (values row + values column) ^ 2 :=
          mul_nonneg entryNonnegative (sq_nonneg _)
        nlinarith [squareNonnegative]
      · have entryNonpositive : matrix row column ≤ 0 := le_of_not_ge entryNonnegative
        rw [abs_of_nonpos entryNonpositive]
        have squareNonpositive : matrix row column *
            (values row - values column) ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg entryNonpositive (sq_nonneg _)
        nlinarith [squareNonpositive]

  have summed_pair_bound :
      -2 * weightedDiagonal ≤ 2 * offDiagonalPart := by
    have rawBound :
        ∑ row, ∑ column,
            -(weight row column * (values row ^ 2 + values column ^ 2)) ≤
          ∑ row, ∑ column,
            2 * offDiagonal row column * values row * values column := by
      exact Finset.sum_le_sum fun row _ =>
        Finset.sum_le_sum fun column _ => pair_bound row column
    have firstWeighted :
        (∑ row, ∑ column, weight row column * values row ^ 2) =
          weightedDiagonal := by
      simp [weightedDiagonal, Finset.sum_mul]
    have secondWeighted :
        (∑ row, ∑ column, weight row column * values column ^ 2) =
          weightedDiagonal := by
      calc
        (∑ row, ∑ column, weight row column * values column ^ 2) =
            ∑ column, ∑ row, weight row column * values column ^ 2 := by
              rw [Finset.sum_comm]
        _ = ∑ column, ∑ row, weight column row * values column ^ 2 := by
              apply Finset.sum_congr rfl
              intro column _
              apply Finset.sum_congr rfl
              intro row _
              rw [weight_symmetric]
        _ = weightedDiagonal := by
              simp [weightedDiagonal, Finset.sum_mul]
    have leftIdentity :
        (∑ row, ∑ column,
            -(weight row column * (values row ^ 2 + values column ^ 2))) =
          -2 * weightedDiagonal := by
      rw [show (∑ row, ∑ column,
          -(weight row column * (values row ^ 2 + values column ^ 2))) =
          -((∑ row, ∑ column, weight row column * values row ^ 2) +
            (∑ row, ∑ column, weight row column * values column ^ 2)) by
        simp_rw [mul_add]
        simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
        ]
      rw [firstWeighted, secondWeighted]
      ring
    have rightIdentity :
        (∑ row, ∑ column,
            2 * offDiagonal row column * values row * values column) =
          2 * offDiagonalPart := by
      unfold offDiagonalPart
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro column _
      ring
    linarith [rawBound]

  have weighted_le_diagonal : weightedDiagonal ≤ diagonalPart := by
    apply Finset.sum_le_sum
    intro row _
    exact mul_le_mul_of_nonneg_right
      (by simpa [weight] using dominant row) (sq_nonneg (values row))

  have diagonal_plus_off_nonnegative : 0 ≤ diagonalPart + offDiagonalPart := by
    linarith [summed_pair_bound, weighted_le_diagonal]

  have quadraticIdentity :
      star values ⬝ᵥ (matrix *ᵥ values) = diagonalPart + offDiagonalPart := by
    simp only [dotProduct, Matrix.mulVec, star_trivial]
    rw [show (∑ row, values row * ∑ column, matrix row column * values column) =
        ∑ row, ∑ column, matrix row column * values row * values column by
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro column _
      ring]
    rw [show (∑ row, ∑ column, matrix row column * values row * values column) =
        diagonalPart + offDiagonalPart by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro row _
      rw [show matrix row row * values row ^ 2 =
          ∑ column, if column = row then matrix row row * values row ^ 2 else 0 by
        simp]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro column _
      by_cases equality : column = row
      · subst column
        simp [offDiagonal, pow_two]
        ring
      · simp [offDiagonal, equality]
      ]
  rw [quadraticIdentity]
  exact diagonal_plus_off_nonnegative

noncomputable section

def factorMatrix : Matrix SectionIndex SectionIndex ℝ := fun row column =>
  (lowerFactorInteger row column : ℝ) / (factorDenominator : ℝ)

def factorGram : Matrix SectionIndex SectionIndex ℝ :=
  factorMatrix * Matrix.transpose factorMatrix

def sectionMatrix : Matrix SectionIndex SectionIndex ℝ := fun row column =>
  (sectionNumerator row column : ℝ) / (commonDenominator : ℝ)

def residualDenominator : ℝ :=
  (commonDenominator : ℝ) * (factorDenominator : ℝ) ^ 2

def residualMatrix : Matrix SectionIndex SectionIndex ℝ := fun row column =>
  (residualNumerator row column : ℝ) / residualDenominator

theorem factorDotInteger_symmetric (row column : SectionIndex) :
    factorDotInteger row column = factorDotInteger column row := by
  simp [factorDotInteger, Nat.min_comm, mul_comm]

theorem sectionNumerator_symmetric (row column : SectionIndex) :
    sectionNumerator row column = sectionNumerator column row := by
  simp [sectionNumerator, upperNumerator, upperIndex, Nat.min_comm, Nat.max_comm]

theorem residualNumerator_symmetric (row column : SectionIndex) :
    residualNumerator row column = residualNumerator column row := by
  unfold residualNumerator
  rw [show sectionUpperIndex row.val column.val =
      sectionUpperIndex column.val row.val by
    simp [sectionUpperIndex, Nat.min_comm, Nat.max_comm]]

theorem residualDenominator_pos : 0 < residualDenominator := by
  unfold residualDenominator
  have commonPositive : (0 : ℝ) < (commonDenominator : ℝ) := by
    exact_mod_cast commonDenominator_pos
  have factorPositive : (0 : ℝ) < (factorDenominator : ℝ) := by
    exact_mod_cast factorDenominator_pos
  positivity

theorem residualMatrix_symmetric : residualMatrix.IsHermitian := by
  ext row column
  simp [Matrix.conjTranspose_apply, residualMatrix,
    residualNumerator_symmetric]

theorem residualMatrix_diagonal_dominant (row : SectionIndex) :
    (∑ column, if column = row then 0 else |residualMatrix row column|) ≤
      residualMatrix row row := by
  have integerMargin := residual_margins_nonnegative row
  have denominatorNonnegative : 0 ≤ residualDenominator := residualDenominator_pos.le
  have castMargin : 0 ≤ (residualMargin row : ℝ) / residualDenominator :=
    div_nonneg (by exact_mod_cast integerMargin) denominatorNonnegative
  have marginIdentity :
      (residualMargin row : ℝ) / residualDenominator =
        residualMatrix row row -
          ∑ column, if column = row then 0 else |residualMatrix row column| := by
    unfold residualMargin residualMatrix
    rw [Int.cast_sub]
    simp_rw [Int.cast_sum]
    simp only [Int.cast_ite, Int.cast_zero]
    rw [sub_div]
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro column _
    by_cases equality : column = row
    · simp [equality]
    · simp [equality, abs_div, abs_of_pos residualDenominator_pos,
        Int.cast_abs]
  rw [marginIdentity] at castMargin
  linarith

theorem residualMatrix_posSemidef : residualMatrix.PosSemidef :=
  posSemidef_of_symmetric_diagonal_dominant residualMatrix
    residualMatrix_symmetric residualMatrix_diagonal_dominant

theorem factorGram_posSemidef : factorGram.PosSemidef := by
  simpa [factorGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose factorMatrix

/-- The shortened triangular dot product equals the full matrix-product sum. -/
theorem factorDotInteger_eq_full_sum (row column : SectionIndex) :
    factorDotInteger row column =
      ∑ pivot : SectionIndex,
        lowerFactorInteger row pivot * lowerFactorInteger column pivot := by
  let bound := min row.val column.val + 1
  have boundLe : bound ≤ sectionDimension := by
    dsimp [bound]
    omega
  have foldAsRange :
      factorDotInteger row column =
        ∑ pivot ∈ Finset.range bound,
          lowerFactorInteger row (Fin.ofNat sectionDimension pivot) *
            lowerFactorInteger column (Fin.ofNat sectionDimension pivot) := by
    unfold factorDotInteger
    change (List.range bound).foldl (fun total pivot => total +
      lowerFactorInteger row (Fin.ofNat sectionDimension pivot) *
        lowerFactorInteger column (Fin.ofNat sectionDimension pivot)) 0 = _
    rw [← List.foldl_map]
    rw [← List.sum_eq_foldl]
    rfl
  rw [foldAsRange]
  let small : Finset SectionIndex :=
    Finset.univ.filter fun pivot => pivot.val ≤ min row.val column.val
  calc
    (∑ pivot ∈ Finset.range bound,
        lowerFactorInteger row (Fin.ofNat sectionDimension pivot) *
          lowerFactorInteger column (Fin.ofNat sectionDimension pivot)) =
        ∑ pivot ∈ small,
          lowerFactorInteger row pivot * lowerFactorInteger column pivot := by
      apply Finset.sum_bij (fun pivot membership =>
        (⟨pivot, lt_of_lt_of_le (Finset.mem_range.mp membership) boundLe⟩ :
          SectionIndex))
      · intro pivot membership
        simp only [small, Finset.mem_filter, Finset.mem_univ, true_and]
        have : pivot < bound := Finset.mem_range.mp membership
        dsimp [bound] at this
        exact Nat.le_of_lt_succ this
      · intro first firstMembership second secondMembership equality
        exact Fin.ext_iff.mp equality
      · intro pivot pivotMembership
        have pivotBound : pivot.val < bound := by
          simpa [small, bound, Nat.lt_succ_iff] using pivotMembership
        refine ⟨pivot.val, Finset.mem_range.mpr pivotBound, ?_⟩
        exact Fin.ext rfl
      · intro pivot membership
        have finEquality : Fin.ofNat sectionDimension pivot =
            (⟨pivot, lt_of_lt_of_le (Finset.mem_range.mp membership) boundLe⟩ :
              SectionIndex) := by
          apply Fin.ext
          simp [Fin.ofNat, Nat.mod_eq_of_lt
            (lt_of_lt_of_le (Finset.mem_range.mp membership) boundLe)]
        rw [finEquality]
    _ = ∑ pivot : SectionIndex,
          lowerFactorInteger row pivot * lowerFactorInteger column pivot := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro pivot _ outside
      have notSmall : ¬ pivot.val ≤ min row.val column.val := by
        intro inequality
        apply outside
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using inequality
      have beyond : min row.val column.val < pivot.val := by
        omega
      have eitherBeyond : row.val < pivot.val ∨ column.val < pivot.val := by
        omega
      rcases eitherBeyond with rowBeyond | columnBeyond
      · simp [lowerFactorInteger, Nat.not_le.mpr rowBeyond]
      · simp [lowerFactorInteger, Nat.not_le.mpr columnBeyond]

theorem factorGram_entry (row column : SectionIndex) :
    factorGram row column =
      (factorDotInteger row column : ℝ) / (factorDenominator : ℝ) ^ 2 := by
  rw [factorGram, Matrix.mul_apply]
  simp only [factorMatrix, Matrix.transpose_apply]
  calc
    (∑ pivot,
        (lowerFactorInteger row pivot : ℝ) / (factorDenominator : ℝ) *
          ((lowerFactorInteger column pivot : ℝ) /
            (factorDenominator : ℝ))) =
        ∑ pivot,
          ((lowerFactorInteger row pivot : ℝ) *
            (lowerFactorInteger column pivot : ℝ)) /
              (factorDenominator : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro pivot _
      ring
    _ = (∑ pivot,
          (lowerFactorInteger row pivot : ℝ) *
            (lowerFactorInteger column pivot : ℝ)) /
              (factorDenominator : ℝ) ^ 2 := by
      rw [Finset.sum_div]
    _ = (factorDotInteger row column : ℝ) /
          (factorDenominator : ℝ) ^ 2 := by
      rw [factorDotInteger_eq_full_sum, Int.cast_sum]
      simp only [Int.cast_mul]

theorem section_decomposition : sectionMatrix = factorGram + residualMatrix := by
  ext row column
  rw [Matrix.add_apply, factorGram_entry]
  unfold sectionMatrix residualMatrix
  rw [residual_entries_exact]
  unfold residualDenominator computedResidualNumerator
  push_cast
  have commonPositive : (0 : ℝ) < (commonDenominator : ℝ) := by
    exact_mod_cast commonDenominator_pos
  have factorPositive : (0 : ℝ) < (factorDenominator : ℝ) := by
    exact_mod_cast factorDenominator_pos
  have commonNonzero : (commonDenominator : ℝ) ≠ 0 := commonPositive.ne'
  have factorNonzero : (factorDenominator : ℝ) ≠ 0 := factorPositive.ne'
  field_simp
  ring

theorem sectionMatrix_posSemidef : sectionMatrix.PosSemidef := by
  rw [section_decomposition]
  exact factorGram_posSemidef.add residualMatrix_posSemidef

def liftMatrix : Matrix FullIndex SectionIndex ℝ :=
  fun row column => Fin.lastCases (-1) (fun row => if row = column then 1 else 0) row

def liftedSection : Matrix FullIndex FullIndex ℝ :=
  fun row => Fin.lastCases
    (fun column => Fin.lastCases
      (∑ first, ∑ second, sectionMatrix first second)
      (fun column => -(∑ first, sectionMatrix first column)) column)
    (fun row column => Fin.lastCases
      (-(∑ second, sectionMatrix row second))
      (fun column => sectionMatrix row column) column) row

theorem liftedSection_eq_congruence :
    liftedSection = liftMatrix * sectionMatrix * liftMatrix.transpose := by
  ext row column
  refine Fin.lastCases ?_ (fun row => ?_) row
  · refine Fin.lastCases ?_ (fun column => ?_) column
    · simp [liftedSection, liftMatrix, Matrix.mul_apply]
      rw [Finset.sum_comm]
    · simp [liftedSection, liftMatrix, Matrix.mul_apply]
  · refine Fin.lastCases ?_ (fun column => ?_) column
    · simp [liftedSection, liftMatrix, Matrix.mul_apply]
    · simp [liftedSection, liftMatrix, Matrix.mul_apply]

theorem liftedSection_posSemidef : liftedSection.PosSemidef := by
  rw [liftedSection_eq_congruence]
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
    sectionMatrix_posSemidef.mul_mul_conjTranspose_same liftMatrix

def fullGramMatrix : Matrix FullIndex FullIndex ℝ := fun row column =>
  (gramMatrix row column : ℝ)

theorem fullGramMatrix_eq_liftedSection : fullGramMatrix = liftedSection := by
  ext row column
  unfold fullGramMatrix
  rw [show gramMatrix row column = liftedSectionRat row column by
    rw [congrFun (congrFun gramMatrix_is_liftedSectionRat row) column]]
  refine Fin.lastCases ?_ (fun row => ?_) row
  · refine Fin.lastCases ?_ (fun column => ?_) column
    · simp [liftedSection, liftedSectionRat, sectionMatrix,
        sectionMatrixRat]
    · simp [liftedSection, liftedSectionRat, sectionMatrix,
        sectionMatrixRat]
  · refine Fin.lastCases ?_ (fun column => ?_) column
    · simp [liftedSection, liftedSectionRat, sectionMatrix,
        sectionMatrixRat]
    · simp [liftedSection, liftedSectionRat, sectionMatrix,
        sectionMatrixRat]

/-- The original exact 325 by 325 Gram matrix is positive semidefinite. -/
theorem fullGramMatrix_posSemidef : fullGramMatrix.PosSemidef := by
  rw [fullGramMatrix_eq_liftedSection]
  exact liftedSection_posSemidef

end

end DH5PSD
