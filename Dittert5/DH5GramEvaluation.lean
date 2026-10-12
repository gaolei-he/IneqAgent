import Dittert5.DH5PSD
import Dittert5.DH5OrbitSum

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace DH5GramEvaluation

open scoped BigOperators
open DH5GramData DH5Symmetry DH5Coefficient DH5OrbitSum DH5PSD Matrix

instance : NeZero dimension := ⟨by native_decide⟩

/-- A matrix variable assignment, indexed by its row and column. -/
abbrev Assignment := Cell -> Real

/-- Recover the matrix cell represented by a zero-based row-major index. -/
def cellOfIndex (index : Nat) : Cell :=
  (Fin.ofNat 5 (index / 5), Fin.ofNat 5 index)

/-- Read a cell assignment as the 25-variable assignment used by sparse polynomials. -/
def flatAssignment (x : Assignment) : Fin 25 -> Real :=
  fun index => x (cellOfIndex index.val)

/-- Evaluate an unordered product of five matrix cells. -/
def monomialValue (x : Assignment) (monomial : DegreeFiveMonomial) : Real :=
  (monomial.1.map x).prod

/-- The two matrix cells in one of the 325 quadratic basis monomials. -/
def basisCells (basisIndex : Fin dimension) : Cell × Cell :=
  let pair := quadraticPairs.getD basisIndex.val (0, 0)
  (cellOfIndex pair.1, cellOfIndex pair.2)

/-- Value of a quadratic basis monomial addressed by a raw array index. -/
def transformedBasisValueAt (x : Assignment) (transformation : Transform)
    (basisIndex : Nat) : Real :=
  let pair := quadraticPairs.getD basisIndex (0, 0)
  x (actCell transformation (cellOfIndex pair.1)) *
    x (actCell transformation (cellOfIndex pair.2))

/-- Value of one quadratic basis monomial after an allowed matrix transformation. -/
def transformedBasisValue (x : Assignment) (transformation : Transform)
    (basisIndex : Fin dimension) : Real :=
  transformedBasisValueAt x transformation basisIndex.val

/-- The full real quadratic form obtained from the exact Gram matrix. -/
def transformedQuadraticForm (x : Assignment) (transformation : Transform) : Real :=
  star (transformedBasisValue x transformation) ⬝ᵥ
    (fullGramMatrix *ᵥ transformedBasisValue x transformation)

/-- One transformed SOS summand, including its transformed distinguished variable. -/
def transformedGramTerm (x : Assignment) (transformation : Transform) : Real :=
  x (actCell transformation ((0, 0) : Cell)) *
    transformedQuadraticForm x transformation

/-- The pair of basis indices stored at one upper-triangular Gram position. -/
def positionPairRaw (position : Fin 52975) : Nat × Nat :=
  gramPairs.getD position.val (0, 0)

/-- An ordered pair whose first index is no larger than its second. -/
abbrev OrderedPair (index : Type) [LE index] :=
  {pair : index × index // pair.1 ≤ pair.2}

/-- The same pair, with its bounds and upper-triangular order recorded in its type. -/
abbrev UpperPair := OrderedPair (Fin dimension)

def positionPairValidAt (position : Nat) : Bool :=
  let pair := gramPairs.getD position (0, 0)
  decide (pair.1 < dimension ∧ pair.2 < dimension ∧ pair.1 ≤ pair.2)

def positionPairValidityAudit : Bool :=
  (List.range 52975).all positionPairValidAt

theorem positionPairValidityAudit_ok : positionPairValidityAudit = true := by
  native_decide

theorem positionPairRaw_valid (position : Fin 52975) :
    let pair := positionPairRaw position
    pair.1 < dimension ∧ pair.2 < dimension ∧ pair.1 ≤ pair.2 := by
  have checked : positionPairValidAt position.val = true :=
    (List.all_eq_true.mp positionPairValidityAudit_ok)
    position.val (List.mem_range.mpr position.isLt)
  simpa [positionPairValidAt, positionPairRaw] using checked

def positionPair (position : Fin 52975) : UpperPair :=
  let pair := positionPairRaw position
  ⟨(Fin.ofNat dimension pair.1, Fin.ofNat dimension pair.2), by
    have facts := positionPairRaw_valid position
    change pair.1 % dimension ≤ pair.2 % dimension
    rw [Nat.mod_eq_of_lt facts.1, Nat.mod_eq_of_lt facts.2.1]
    exact facts.2.2⟩

def positionPairIndexAt (position : Nat) : Bool :=
  let pair := gramPairs.getD position (0, 0)
  decide (upperIndex pair.1 pair.2 = position)

def positionPairIndexAudit : Bool :=
  (List.range 52975).all positionPairIndexAt

theorem positionPairIndexAudit_ok : positionPairIndexAudit = true := by
  native_decide

theorem positionPair_index (position : Fin 52975) :
    upperIndex (positionPair position).1.1.val (positionPair position).1.2.val =
      position.val := by
  have facts := positionPairRaw_valid position
  have checked : positionPairIndexAt position.val = true :=
    (List.all_eq_true.mp positionPairIndexAudit_ok)
    position.val (List.mem_range.mpr position.isLt)
  change upperIndex
    ((positionPairRaw position).1 % dimension)
    ((positionPairRaw position).2 % dimension) = position.val
  rw [Nat.mod_eq_of_lt facts.1, Nat.mod_eq_of_lt facts.2.1]
  simpa [positionPairIndexAt, positionPairRaw] using checked

def pairLookupAt (row column : Nat) : Bool :=
  if ordered : row ≤ column then
    let position := upperIndex row column
    decide (position < 52975 ∧ gramPairs.getD position (0, 0) = (row, column))
  else true

def pairLookupAudit : Bool :=
  (List.range dimension).all fun row =>
    (List.range dimension).all fun column => pairLookupAt row column

theorem pairLookupAudit_ok : pairLookupAudit = true := by
  native_decide

theorem pairLookup_exact (row column : Fin dimension) (ordered : row ≤ column) :
    upperIndex row.val column.val < 52975 ∧
      gramPairs.getD (upperIndex row.val column.val) (0, 0) =
        (row.val, column.val) := by
  have rows :
      (List.range dimension).all (fun currentColumn =>
        pairLookupAt row.val currentColumn) = true :=
    (List.all_eq_true.mp pairLookupAudit_ok)
    row.val (List.mem_range.mpr row.isLt)
  have checked : pairLookupAt row.val column.val = true :=
    (List.all_eq_true.mp rows)
    column.val (List.mem_range.mpr column.isLt)
  simpa [pairLookupAt, ordered] using checked

def pairPosition (pair : UpperPair) : Fin 52975 :=
  ⟨upperIndex pair.1.1.val pair.1.2.val,
    (pairLookup_exact pair.1.1 pair.1.2 pair.2).1⟩

theorem positionPair_pairPosition (pair : UpperPair) :
    positionPair (pairPosition pair) = pair := by
  have lookup := pairLookup_exact pair.1.1 pair.1.2 pair.2
  have rawEquality : positionPairRaw (pairPosition pair) =
      (pair.1.1.val, pair.1.2.val) := by
    simpa [positionPairRaw, pairPosition] using lookup.2
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · change (positionPairRaw (pairPosition pair)).1 % dimension = pair.1.1.val
    rw [rawEquality]
    exact Nat.mod_eq_of_lt pair.1.1.isLt
  · change (positionPairRaw (pairPosition pair)).2 % dimension = pair.1.2.val
    rw [rawEquality]
    exact Nat.mod_eq_of_lt pair.1.2.isLt

theorem pairPosition_positionPair (position : Fin 52975) :
    pairPosition (positionPair position) = position := by
  apply Fin.ext
  change upperIndex (positionPair position).1.1.val
    (positionPair position).1.2.val = position.val
  exact positionPair_index position

/-- The stored list enumerates every upper-triangular pair exactly once. -/
theorem positionPair_injective : Function.Injective positionPair := by
  intro first second equality
  rw [← pairPosition_positionPair first,
    ← pairPosition_positionPair second, equality]

theorem positionPair_bijective : Function.Bijective positionPair := by
  exact ⟨positionPair_injective, fun pair =>
    ⟨pairPosition pair, positionPair_pairPosition pair⟩⟩

noncomputable def positionEquiv : Fin 52975 ≃ UpperPair :=
  Equiv.ofBijective positionPair positionPair_bijective

/-- The five cells occurring in the monomial belonging to one Gram position. -/
def positionFactorsAt (position : Nat) : Factors :=
  let pair := gramPairs.getD position (0, 0)
  let first := quadraticPairs.getD pair.1 (0, 0)
  let second := quadraticPairs.getD pair.2 (0, 0)
  ![((0, 0) : Cell), cellOfIndex first.1, cellOfIndex first.2,
    cellOfIndex second.1, cellOfIndex second.2]

def positionFactors (position : Fin 52975) : Factors :=
  positionFactorsAt position.val

def positionMonomial (position : Fin 52975) : DegreeFiveMonomial :=
  monomialOfFactors (positionFactors position)

def positionMonomialKeyAt (position : Nat) : Bool :=
  decide (monomialOfFactors (positionFactorsAt position) =
    monomialOfKey (gramMonomialKey position))

def positionMonomialKeyAudit : Bool :=
  (List.range 52975).all positionMonomialKeyAt

theorem positionMonomialKeyAudit_ok : positionMonomialKeyAudit = true := by
  native_decide

/-- The key exported with the certificate decodes to the intended five factors. -/
theorem positionMonomial_eq_keyMonomial : forall position : Fin 52975,
    positionMonomial position =
      monomialOfKey (gramMonomialKey position.val) := by
  intro position
  have checked : positionMonomialKeyAt position.val = true :=
    (List.all_eq_true.mp positionMonomialKeyAudit_ok)
      position.val (List.mem_range.mpr position.isLt)
  simpa [positionMonomialKeyAt, positionMonomial, positionFactors] using checked

theorem positionPair_values (position : Fin 52975) :
    ((positionPair position).1.1.val, (positionPair position).1.2.val) =
      positionPairRaw position := by
  have facts := positionPairRaw_valid position
  apply Prod.ext
  · change (positionPairRaw position).1 % dimension = (positionPairRaw position).1
    exact Nat.mod_eq_of_lt facts.1
  · change (positionPairRaw position).2 % dimension = (positionPairRaw position).2
    exact Nat.mod_eq_of_lt facts.2.1

theorem monomialValue_monomialOfFactors (x : Assignment) (factors : Factors) :
    monomialValue x (monomialOfFactors factors) =
      ∏ index, x (factors index) := by
  change (List.ofFn fun index => x (factors index)).prod = _
  exact List.prod_ofFn

theorem keyDigit_lt (key : Nat) (factor : Fin 5) :
    keyDigit key factor < 25 := by
  exact Nat.mod_lt _ (by norm_num)

theorem factor_cell_eq (key : Nat) (factor : Fin 5) :
    cellOfIndex (keyCellIndex key factor).val = factorsOfKey key factor := by
  have digitLt := keyDigit_lt key factor
  simp only [keyCellIndex, Fin.ofNat, Nat.mod_eq_of_lt digitLt]
  unfold cellOfIndex factorsOfKey
  rfl

/-- Decoding five factors and counting their 25 variable indices give the same monomial value. -/
theorem monomialValue_monomialOfKey (x : Assignment) (key : Nat) :
    monomialValue x (monomialOfKey key) =
      SparsePolyCheck.monomial (flatAssignment x) (keyExponent key) := by
  unfold monomialOfKey
  rw [monomialValue_monomialOfFactors]
  simp_rw [← factor_cell_eq key]
  unfold SparsePolyCheck.monomial keyExponent
  rw [← List.prod_ofFn]
  let indices : List (Fin 25) :=
    List.ofFn fun factor : Fin 5 => keyCellIndex key factor
  change (indices.map (flatAssignment x)).prod =
    ∏ current : Fin 25, flatAssignment x current ^ indices.count current
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (by simp)
  intro current _ notIn
  rw [List.count_eq_zero_of_not_mem]
  · simp
  · simpa using notIn

theorem monomialValue_map (x : Assignment) (transformation : Transform)
    (monomial : DegreeFiveMonomial) :
    monomialValue x (actMonomial transformation monomial) =
      monomialValue (fun cell => x (actCell transformation cell)) monomial := by
  simp [monomialValue, actMonomial, Multiset.map_map, Function.comp_def]

theorem transformed_position_monomial_value (x : Assignment)
    (transformation : Transform) (position : Fin 52975) :
    monomialValue x (actMonomial transformation (positionMonomial position)) =
      x (actCell transformation ((0, 0) : Cell)) *
        transformedBasisValueAt x transformation (positionPairRaw position).1 *
        transformedBasisValueAt x transformation (positionPairRaw position).2 := by
  rw [monomialValue_map, positionMonomial, monomialValue_monomialOfFactors]
  simp [positionFactors, positionFactorsAt, positionPairRaw, transformedBasisValueAt,
    Fin.prod_univ_succ]
  ring

theorem transformed_position_monomial_value_typed (x : Assignment)
    (transformation : Transform) (position : Fin 52975) :
    monomialValue x (actMonomial transformation (positionMonomial position)) =
      x (actCell transformation ((0, 0) : Cell)) *
        transformedBasisValue x transformation (positionPair position).1.1 *
        transformedBasisValue x transformation (positionPair position).1.2 := by
  rw [transformed_position_monomial_value]
  have values := positionPair_values position
  have first := congrArg Prod.fst values
  have second := congrArg Prod.snd values
  unfold transformedBasisValue
  rw [← first, ← second]

/-- A symmetric double sum can be written using each upper-triangular pair once. -/
theorem sum_upper_triangle {index : Type} [Fintype index] [LinearOrder index]
    (term : index -> index -> Real)
    (symmetric : forall first second, term first second = term second first) :
    (∑ first, ∑ second, term first second) =
      ∑ first, ∑ second,
        if first ≤ second then
          (if first = second then 1 else 2) * term first second
        else 0 := by
  let diagonal : Real := ∑ first, ∑ second,
    if first = second then term first second else 0
  let upper : Real := ∑ first, ∑ second,
    if first < second then term first second else 0
  let lower : Real := ∑ first, ∑ second,
    if second < first then term first second else 0
  have lower_eq_upper : lower = upper := by
    calc
      lower = ∑ second, ∑ first,
          if second < first then term first second else 0 := by
            simp only [lower]
            rw [Finset.sum_comm]
      _ = ∑ first, ∑ second,
          if first < second then term second first else 0 := rfl
      _ = upper := by
        unfold upper
        apply Finset.sum_congr rfl
        intro first _
        apply Finset.sum_congr rfl
        intro second _
        split
        · rw [symmetric]
        · rfl
  have split_all :
      (∑ first, ∑ second, term first second) = diagonal + upper + lower := by
    simp only [diagonal, upper, lower]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    rcases lt_trichotomy first second with less | equal | greater
    · simp [less, ne_of_lt less, not_lt_of_ge less.le]
    · subst second
      simp
    · simp [greater, ne_of_gt greater, not_lt_of_ge greater.le,
        not_le_of_gt greater]
  have split_upper :
      (∑ first, ∑ second,
        if first ≤ second then
          (if first = second then 1 else 2) * term first second
        else 0) = diagonal + upper + upper := by
    simp only [diagonal, upper]
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro second _
    rcases lt_trichotomy first second with less | equal | greater
    · simp [less, less.le, ne_of_lt less]
      ring
    · subst second
      simp
    · simp [not_le_of_gt greater, not_lt_of_ge greater.le,
        ne_of_gt greater]
  rw [split_all, split_upper, lower_eq_upper]

def orderedPairTerm {index : Type} [DecidableEq index] [LE index]
    (matrix : Matrix index index Real) (values : index -> Real)
    (pair : OrderedPair index) : Real :=
  (if pair.1.1 = pair.1.2 then 1 else 2) *
    matrix pair.1.1 pair.1.2 * values pair.1.1 * values pair.1.2

theorem sum_orderedPairTerm {index : Type} [Fintype index] [LinearOrder index]
    (matrix : Matrix index index Real) (values : index -> Real)
    (symmetric : matrix.IsHermitian) :
    (∑ pair : OrderedPair index, orderedPairTerm matrix values pair) =
      ∑ first, ∑ second, matrix first second * values first * values second := by
  have termSymmetric : forall first second,
      matrix first second * values first * values second =
        matrix second first * values second * values first := by
    intro first second
    have entryEquality : matrix first second = matrix second first := by
      have equality := congrFun (congrFun symmetric first) second
      simpa [Matrix.conjTranspose_apply] using equality.symm
    rw [entryEquality]
    ring
  rw [sum_upper_triangle
    (fun first second => matrix first second * values first * values second)
    termSymmetric]
  let upperFinset : Finset (index × index) :=
    Finset.univ.filter fun pair => pair.1 ≤ pair.2
  let summand : index × index -> Real := fun pair =>
    (if pair.1 = pair.2 then 1 else 2) *
      matrix pair.1 pair.2 * values pair.1 * values pair.2
  have subtypeSum :
      (∑ pair : OrderedPair index, orderedPairTerm matrix values pair) =
        ∑ pair ∈ upperFinset, summand pair := by
    symm
    simpa only [orderedPairTerm, summand] using
      (Finset.sum_subtype upperFinset
        (by
          intro pair
          simp only [upperFinset, Finset.mem_filter, Finset.mem_univ, true_and])
        summand)
  rw [subtypeSum]
  rw [show (∑ pair ∈ upperFinset, summand pair) =
      ∑ pair ∈ (Finset.univ : Finset (index × index)),
        if pair.1 ≤ pair.2 then summand pair else 0 by
    exact Finset.sum_filter (fun pair : index × index =>
      pair.1 ≤ pair.2) summand]
  rw [show (Finset.univ : Finset (index × index)) =
      (Finset.univ : Finset index) ×ˢ Finset.univ by
    exact Finset.univ_product_univ.symm]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  by_cases ordered : first ≤ second
  · by_cases equal : first = second
    · simp [summand, ordered, equal]
    · simp [summand, ordered, equal]
      ring
  · simp [summand, ordered]

theorem sum_reindexed_orderedPairTerm
    {position index : Type} [Fintype position] [Fintype index] [LinearOrder index]
    (reindex : position ≃ OrderedPair index)
    (matrix : Matrix index index Real) (values : index -> Real)
    (symmetric : matrix.IsHermitian) :
    (∑ current : position, orderedPairTerm matrix values (reindex current)) =
      ∑ first, ∑ second, matrix first second * values first * values second := by
  calc
    (∑ current : position, orderedPairTerm matrix values (reindex current)) =
        ∑ pair : OrderedPair index, orderedPairTerm matrix values pair :=
      Equiv.sum_comp reindex (orderedPairTerm matrix values)
    _ = _ := sum_orderedPairTerm matrix values symmetric

theorem dotProduct_mulVec_eq_doubleSum
    {index : Type} [Fintype index]
    (matrix : Matrix index index Real) (values : index -> Real) :
    star values ⬝ᵥ (matrix *ᵥ values) =
      ∑ first, ∑ second, matrix first second * values first * values second := by
  simp only [dotProduct, Matrix.mulVec, star_trivial]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second _
  ring

def upperPairTerm (matrix : Matrix (Fin dimension) (Fin dimension) Real)
    (values : Fin dimension -> Real) (pair : UpperPair) : Real :=
  orderedPairTerm matrix values pair

/-- Upper-triangular expansion of one transformed Gram quadratic form. -/
def transformedUpperGramTerm (x : Assignment) (transformation : Transform) : Real :=
  x (actCell transformation ((0, 0) : Cell)) *
    ∑ position : Fin 52975,
      upperPairTerm fullGramMatrix (transformedBasisValue x transformation)
        (positionPair position)

theorem transformedQuadraticForm_eq_upperSum (x : Assignment)
    (transformation : Transform) :
    transformedQuadraticForm x transformation =
      ∑ position : Fin 52975,
        upperPairTerm fullGramMatrix (transformedBasisValue x transformation)
          (positionPair position) := by
  calc
    transformedQuadraticForm x transformation =
        ∑ first, ∑ second,
          fullGramMatrix first second * transformedBasisValue x transformation first *
            transformedBasisValue x transformation second := by
      exact dotProduct_mulVec_eq_doubleSum fullGramMatrix
        (transformedBasisValue x transformation)
    _ = ∑ position : Fin 52975,
          upperPairTerm fullGramMatrix (transformedBasisValue x transformation)
            (positionPair position) := by
      exact (sum_reindexed_orderedPairTerm positionEquiv fullGramMatrix
        (transformedBasisValue x transformation)
        fullGramMatrix_posSemidef.isHermitian).symm

theorem transformedGramTerm_eq_upper (x : Assignment)
    (transformation : Transform) :
    transformedGramTerm x transformation =
      transformedUpperGramTerm x transformation := by
  unfold transformedGramTerm transformedUpperGramTerm
  rw [transformedQuadraticForm_eq_upperSum]

noncomputable def positionCoefficient (position : Fin 52975) : Real :=
  (gramSymmetryFactor position.val : Real) *
    (upperNumerators.getD position.val 0 : Real) /
      (commonDenominator : Real)

theorem fullGramMatrix_position (position : Fin 52975) :
    fullGramMatrix (positionPair position).1.1 (positionPair position).1.2 =
      (upperNumerators.getD position.val 0 : Real) /
        (commonDenominator : Real) := by
  unfold fullGramMatrix gramMatrix DH5GramData.gram upperNumerator
  rw [positionPair_index position]
  norm_num

theorem gramSymmetryFactor_real (position : Fin 52975) :
    (gramSymmetryFactor position.val : Real) =
      if (positionPair position).1.1 = (positionPair position).1.2 then 1 else 2 := by
  have values := positionPair_values position
  have equality :
      ((positionPair position).1.1 = (positionPair position).1.2) =
        ((positionPairRaw position).1 = (positionPairRaw position).2) := by
    apply propext
    simp only [Fin.ext_iff]
    have first : (positionPair position).1.1.val =
        (positionPairRaw position).1 := by
      simpa using congrArg Prod.fst values
    have second : (positionPair position).1.2.val =
        (positionPairRaw position).2 := by
      simpa using congrArg Prod.snd values
    rw [first, second]
  simp only [equality]
  unfold gramSymmetryFactor positionPairRaw
  split <;> simp_all

theorem transformedGramTerm_eq_position_sum (x : Assignment)
    (transformation : Transform) :
    transformedGramTerm x transformation =
      ∑ position : Fin 52975,
        positionCoefficient position *
          monomialValue x (actMonomial transformation (positionMonomial position)) := by
  rw [transformedGramTerm_eq_upper]
  unfold transformedUpperGramTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro position _
  unfold upperPairTerm orderedPairTerm positionCoefficient
  rw [fullGramMatrix_position, gramSymmetryFactor_real,
    transformed_position_monomial_value_typed]
  ring

end DH5GramEvaluation
