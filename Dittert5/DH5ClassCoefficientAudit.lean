import Dittert5.DH5Coefficient

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace DH5ClassCoefficientAudit

open DH5GramData DH5Symmetry DH5Coefficient

/-- The integer numerator contributed by one upper-triangular Gram position to one class. -/
def positionNumeratorAt (classId : Fin classCount) (position : Nat) : Int :=
  if gramClassId position = classId then
    gramSymmetryFactor position * upperNumerators.getD position 0
  else 0

/-- The exact Gram numerator obtained by summing all positions assigned to one class. -/
def classNumerator (classId : Fin classCount) : Int :=
  (List.range 52975).foldl
    (fun total position => total + positionNumeratorAt classId position) 0

/-- The direct per-class sum agrees with the single-pass accumulator already audited upstream. -/
theorem classNumerator_eq_computed :
    ∀ classId : Fin classCount,
      classNumerator classId =
        computedClassNumerators.getD classId.val 0 := by
  native_decide

end DH5ClassCoefficientAudit
