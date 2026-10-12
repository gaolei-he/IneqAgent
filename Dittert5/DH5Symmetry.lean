import Dittert5.DH5GramData

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace DH5Symmetry

open DH5GramData

abbrev Side := Fin 5
abbrev Cell := Side × Side
abbrev Factors := Fin 5 → Cell

/-- One allowed operation: independently permute rows and columns, then optionally transpose. -/
structure Transform where
  rowPermutation : Equiv.Perm Side
  columnPermutation : Equiv.Perm Side
  transposed : Bool
  deriving DecidableEq, Fintype

/-- Apply one allowed operation to a matrix position. -/
def actCell (transformation : Transform) (cell : Cell) : Cell :=
  if transformation.transposed then
    (transformation.columnPermutation cell.2,
      transformation.rowPermutation cell.1)
  else
    (transformation.rowPermutation cell.1,
      transformation.columnPermutation cell.2)

def actFactors (transformation : Transform) (factors : Factors) : Factors :=
  fun index => actCell transformation (factors index)

/-- Composition is chosen so that `compose outer inner` first applies `inner`. -/
def compose (outer inner : Transform) : Transform :=
  match outer.transposed, inner.transposed with
  | false, false =>
      ⟨inner.rowPermutation.trans outer.rowPermutation,
       inner.columnPermutation.trans outer.columnPermutation, false⟩
  | false, true =>
      ⟨inner.rowPermutation.trans outer.columnPermutation,
       inner.columnPermutation.trans outer.rowPermutation, true⟩
  | true, false =>
      ⟨inner.rowPermutation.trans outer.rowPermutation,
       inner.columnPermutation.trans outer.columnPermutation, true⟩
  | true, true =>
      ⟨inner.rowPermutation.trans outer.columnPermutation,
       inner.columnPermutation.trans outer.rowPermutation, false⟩

/-- Explicit inverse of an allowed operation. -/
def inverse (transformation : Transform) : Transform :=
  if transformation.transposed then
    ⟨transformation.columnPermutation.symm,
     transformation.rowPermutation.symm, true⟩
  else
    ⟨transformation.rowPermutation.symm,
     transformation.columnPermutation.symm, false⟩

@[simp] theorem actCell_compose (outer inner : Transform) (cell : Cell) :
    actCell (compose outer inner) cell = actCell outer (actCell inner cell) := by
  rcases outer with ⟨outerRow, outerColumn, outerTranspose⟩
  rcases inner with ⟨innerRow, innerColumn, innerTranspose⟩
  rcases cell with ⟨row, column⟩
  cases outerTranspose <;> cases innerTranspose <;>
    simp [actCell, compose]

@[simp] theorem actCell_inverse_left (transformation : Transform) (cell : Cell) :
    actCell (inverse transformation) (actCell transformation cell) = cell := by
  rcases transformation with ⟨rowPermutation, columnPermutation, transposed⟩
  rcases cell with ⟨row, column⟩
  cases transposed <;> simp [actCell, inverse]

@[simp] theorem actCell_inverse_right (transformation : Transform) (cell : Cell) :
    actCell transformation (actCell (inverse transformation) cell) = cell := by
  rcases transformation with ⟨rowPermutation, columnPermutation, transposed⟩
  rcases cell with ⟨row, column⟩
  cases transposed <;> simp [actCell, inverse]

@[simp] theorem actFactors_compose (outer inner : Transform) (factors : Factors) :
    actFactors (compose outer inner) factors =
      actFactors outer (actFactors inner factors) := by
  funext index
  exact actCell_compose outer inner (factors index)

/-- Zero-based row-major cell number. -/
def cellIndex (cell : Cell) : Nat := 5 * cell.1.val + cell.2.val

/-- Encode five factors after sorting their cell numbers. -/
def factorsKey (factors : Factors) : Nat :=
  let cells := (List.ofFn fun index => cellIndex (factors index)).mergeSort
    (fun left right => decide (left ≤ right))
  cells.foldl (fun key cell => 25 * key + cell) 0

def keyDigit (key : Nat) (index : Fin 5) : Nat :=
  (key / 25 ^ (4 - index.val)) % 25

/-- Decode a stored base-25 key into its five canonical factors. -/
def factorsOfKey (key : Nat) : Factors := fun index =>
  let digit := keyDigit key index
  (Fin.ofNat 5 (digit / 5), Fin.ofNat 5 digit)

def transformKey (transformation : Transform) (key : Nat) : Nat :=
  factorsKey (actFactors transformation (factorsOfKey key))

def representativeKey (classId : Fin classCount) : Nat :=
  representativeKeys.getD classId.val 0

def classSize (classId : Fin classCount) : Nat :=
  classSizes.getD classId.val 0

def classRepetition (classId : Fin classCount) : Nat :=
  classRepetitions.getD classId.val 0

def orbitStart (classId : Fin classCount) : Nat :=
  orbitOffsets.getD classId.val 0

def orbitStop (classId : Fin classCount) : Nat :=
  orbitOffsets.getD (classId.val + 1) 0

/-- Fast membership test in the sorted slice belonging to one class. -/
def orbitContains (classId : Fin classCount) (key : Nat) : Bool :=
  orbitKeys.binSearchContains key (fun left right => left < right)
    (orbitStart classId) (orbitStop classId - 1)

def orbitList (classId : Fin classCount) : List Nat :=
  (orbitKeys.extract (orbitStart classId) (orbitStop classId)).toList

def stabilizerCount (classId : Fin classCount) : Nat :=
  (Finset.univ.filter fun transformation : Transform =>
    transformKey transformation (representativeKey classId) =
      representativeKey classId).card

/-- There are exactly 120 row permutations, 120 column permutations and two transpose choices. -/
theorem transform_card : Fintype.card Transform = transformationCount := by
  native_decide

/-- Every stored class slice has the declared size and the slices cover the payload exactly. -/
theorem orbit_slice_sizes :
    ∀ classId : Fin classCount,
      orbitStop classId - orbitStart classId = classSize classId := by
  native_decide

/-- Every class slice is strictly increasing, hence contains no duplicate monomial key. -/
theorem orbit_slices_strictly_increasing :
    ∀ classId : Fin classCount,
      (orbitList classId).Pairwise (fun left right => left < right) := by
  native_decide

/-- Every transformed representative is present in its stored, sorted orbit slice. -/
theorem transformed_representatives_are_stored :
    ∀ classId : Fin classCount, ∀ transformation : Transform,
      orbitContains classId
        (transformKey transformation (representativeKey classId)) = true := by
  native_decide

/-- The stored multiplicity is the exact number of transformations fixing the representative. -/
theorem exact_stabilizer_counts :
    ∀ classId : Fin classCount,
      stabilizerCount classId = classRepetition classId := by
  native_decide

/-- Orbit size times common fiber size is all 28,800 transformations. -/
theorem orbit_size_times_repetition :
    ∀ classId : Fin classCount,
      classSize classId * classRepetition classId = transformationCount := by
  native_decide

end DH5Symmetry
