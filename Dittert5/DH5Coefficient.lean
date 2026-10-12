import Dittert5.DH5Symmetry
import Dittert5.FastPolyForSOS

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace DH5Coefficient

open DH5GramData DH5Symmetry SparsePolyCheck

abbrev P := Poly 25

instance : NeZero classCount := ⟨by native_decide⟩

def triangularPairs (size : Nat) : Array (Nat × Nat) :=
  ((List.range size).flatMap fun first =>
    (List.range (size - first)).map fun offset => (first, first + offset)).toArray

/-- The 325 quadratic basis elements, each represented by its two variable indices. -/
def quadraticPairs : Array (Nat × Nat) := triangularPairs 25

/-- The 52,975 upper-triangular positions of the symmetric Gram matrix. -/
def gramPairs : Array (Nat × Nat) := triangularPairs dimension

theorem quadraticPairs_size : quadraticPairs.size = dimension := by native_decide
theorem gramPairs_size : gramPairs.size = 52975 := by native_decide

def cellsKey (cells : List Nat) : Nat :=
  let sorted := cells.mergeSort (fun left right => decide (left ≤ right))
  sorted.foldl (fun key cell => 25 * key + cell) 0

/-- Monomial key of `x11 * basis[first] * basis[second]`. -/
def gramMonomialKey (position : Nat) : Nat :=
  let pair := gramPairs.getD position (0, 0)
  let firstBasis := quadraticPairs.getD pair.1 (0, 0)
  let secondBasis := quadraticPairs.getD pair.2 (0, 0)
  cellsKey [0, firstBasis.1, firstBasis.2, secondBasis.1, secondBasis.2]

def gramClassId (position : Nat) : Fin classCount :=
  Fin.ofNat classCount (gramClassIds.getD position 0)

/-- Every upper-triangular Gram entry is assigned to an orbit that really contains its monomial. -/
theorem gram_class_assignments_valid :
    ∀ position : Fin 52975,
      orbitContains (gramClassId position.val) (gramMonomialKey position.val) = true := by
  native_decide

def gramSymmetryFactor (position : Nat) : Int :=
  let pair := gramPairs.getD position (0, 0)
  if pair.1 = pair.2 then 1 else 2

/-- Accumulate the exact integer Gram numerator separately in each of the 54 classes. -/
def computedClassNumerators : Array Int :=
  let initial := Array.replicate classCount 0
  let result := gramPairs.foldl (fun state _ =>
    let position := state.1
    let output := state.2
    let classId := gramClassIds.getD position 0
    let contribution := gramSymmetryFactor position * upperNumerators.getD position 0
    let output := output.setIfInBounds classId
      (output.getD classId 0 + contribution)
    (position + 1, output)) (0, initial)
  result.2

def targetCoefficient (classId : Fin classCount) : Int :=
  classTargets.getD classId.val 0

/-- These are the 54 exact coefficient equations, cleared of the common denominator. -/
theorem exact_gram_coefficient_equations :
    ∀ classId : Fin classCount,
      (classRepetition classId : Int) *
          computedClassNumerators.getD classId.val 0 =
        targetCoefficient classId * commonDenominator := by
  native_decide

def keyCellIndex (key : Nat) (factor : Fin 5) : Fin 25 :=
  Fin.ofNat 25 (keyDigit key factor)

def keyExponent (key : Nat) : Exp 25 := fun current =>
  (List.ofFn fun factor : Fin 5 => keyCellIndex key factor).count current

def orbitTerm (classId : Fin classCount) (key : Nat) : Term 25 :=
  { exp := keyExponent key, coeff := (targetCoefficient classId : ℚ) }

def orbitClassPoly (classId : Fin classCount) : P :=
  (orbitList classId).map (orbitTerm classId)

/-- The compressed polynomial: one copy of every monomial in every orbit. -/
def orbitTargetPoly : P :=
  (List.ofFn orbitClassPoly).flatten

def polySum : List P → P
  | [] => []
  | poly :: rest => FastPolyForSOS.fastAdd poly (polySum rest)

def polyProduct : List P → P
  | [] => const 1
  | poly :: rest => FastPolyForSOS.fastMul poly (polyProduct rest)

def allVariables : P :=
  polySum ((List.range 25).map fun index => var (Fin.ofNat 25 index))

def rowSum (row : Fin 5) : P :=
  polySum ((List.range 5).map fun column => var (Fin.ofNat 25 (5 * row.val + column)))

def columnSum (column : Fin 5) : P :=
  polySum ((List.range 5).map fun row => var (Fin.ofNat 25 (5 * row + column.val)))

def rowProduct : P :=
  polyProduct (List.ofFn rowSum)

def columnProduct : P :=
  polyProduct (List.ofFn columnSum)

def keyMonomial (key : Nat) : P :=
  monoPoly (keyExponent key)

def permanentPoly : P :=
  polySum (permanentKeys.toList.map keyMonomial)

def phiPoly : P :=
  sub (FastPolyForSOS.fastAdd rowProduct columnProduct) permanentPoly

def allVariablesPowerFive : P :=
  FastPolyForSOS.fastPow allVariables 5

/-- The original homogeneous DH5 polynomial `H5 = 1226*s^5 - 1953125*phi`. -/
def h5Poly : P :=
  sub (scale 1226 allVariablesPowerFive)
    (scale 1953125 phiPoly)

/-- The sum of the squares of all 25 matrix variables. -/
def variableSquareSum : P :=
  polySum ((List.range 25).map fun index =>
    FastPolyForSOS.fastSquare (var (Fin.ofNat 25 index)))

/-- `G = s^3 * sum((25*x_ij-s)^2) = 625*s^3*sum(x_ij^2)-25*s^5`. -/
def uniquenessGapPoly : P :=
  sub
    (scale 625 (FastPolyForSOS.fastMul
      (FastPolyForSOS.fastPow allVariables 3) variableSquareSum))
    (scale 25 allVariablesPowerFive)

/-- The integer-scaled strengthened target `100*H5-G`. -/
def compactTargetPoly : P :=
  sub (scale 100 h5Poly) uniquenessGapPoly

/-- Independent expansion check: the 54 orbit coefficients are exactly `100*H5-G`. -/
theorem orbit_target_is_scaled_margin :
    FastPolyForSOS.fastNormalize orbitTargetPoly =
      FastPolyForSOS.fastNormalize compactTargetPoly := by
  native_decide

end DH5Coefficient
