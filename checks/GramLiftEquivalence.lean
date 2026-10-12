import Dittert5.DH5GramLiftAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators
open DH5GramData DH5PSDAudit DH5GramLiftAudit Matrix
example : liftedSectionRat =
  (fun row => Fin.lastCases
    (fun column => Fin.lastCases
      (∑ first, ∑ second, sectionMatrixRat first second)
      (fun column => -(∑ first, sectionMatrixRat first column)) column)
    (fun row column => Fin.lastCases
      (-(∑ second, sectionMatrixRat row second))
      (fun column => sectionMatrixRat row column) column) row) := by
  funext row column
  refine Fin.lastCases ?_ (fun row => ?_) row <;>
    refine Fin.lastCases ?_ (fun column => ?_) column <;> simp only [liftedSectionRat, Fin.lastCases_last, Fin.lastCases_castSucc]
