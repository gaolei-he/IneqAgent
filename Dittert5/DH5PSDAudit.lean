import Dittert5.DH5Coefficient

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace DH5PSDAudit

open scoped BigOperators
open DH5GramData

abbrev SectionIndex := Fin sectionDimension

instance : NeZero sectionDimension := ⟨by native_decide⟩

def lowerIndex (row column : Nat) : Nat := row * (row + 1) / 2 + column

def lowerFactorInteger (row column : SectionIndex) : Int :=
  if column.val ≤ row.val then
    lowerFactorEntries.getD (lowerIndex row.val column.val) 0
  else
    0

def factorDotInteger (row column : SectionIndex) : Int :=
  (List.range (min row.val column.val + 1)).foldl
    (fun total pivot => total +
      lowerFactorInteger row (Fin.ofNat sectionDimension pivot) *
        lowerFactorInteger column (Fin.ofNat sectionDimension pivot)) 0

def sectionNumerator (row column : SectionIndex) : Int :=
  upperNumerator row.castSucc column.castSucc

def computedResidualNumerator (row column : SectionIndex) : Int :=
  sectionNumerator row column * factorDenominator ^ 2 -
    commonDenominator * factorDotInteger row column

def sectionUpperIndex (row column : Nat) : Nat :=
  let first := min row column
  let second := max row column
  first * sectionDimension - first * (first - 1) / 2 + (second - first)

def residualNumerator (row column : SectionIndex) : Int :=
  residualUpperEntries.getD (sectionUpperIndex row.val column.val) 0

/-- Lean recomputes the factor product and checks every stored residual entry exactly. -/
theorem residual_entries_exact :
    ∀ row column : SectionIndex,
      residualNumerator row column = computedResidualNumerator row column := by
  native_decide

def residualMargin (row : SectionIndex) : Int :=
  residualNumerator row row -
    ∑ column : SectionIndex,
      if column = row then 0 else |residualNumerator row column|

/-- The independently stored exact residual is diagonally dominant in every row. -/
theorem residual_margins_nonnegative :
    ∀ row : SectionIndex, 0 ≤ residualMargin row := by
  native_decide

end DH5PSDAudit
