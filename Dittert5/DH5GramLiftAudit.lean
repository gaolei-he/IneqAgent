import Dittert5.DH5PSDAudit

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace DH5GramLiftAudit

open scoped BigOperators
open DH5GramData DH5PSDAudit Matrix

abbrev FullIndex := Fin (sectionDimension + 1)

def sectionMatrixRat : Matrix SectionIndex SectionIndex ℚ := fun row column =>
  (sectionNumerator row column : ℚ) / (commonDenominator : ℚ)

-- Delay finite sums until the selected last-row/last-column case is evaluated.
-- This retains the same matrix entries while avoiding eager discarded sums.
def liftedSectionRat : Matrix FullIndex FullIndex ℚ :=
  fun row => Fin.lastCases
    (fun column => Fin.lastCases
      (fun _ : Unit => ∑ first, ∑ second, sectionMatrixRat first second)
      (fun column _ => -(∑ first, sectionMatrixRat first column)) column ())
    (fun row column => Fin.lastCases
      (fun _ : Unit => -(∑ second, sectionMatrixRat row second))
      (fun column _ => sectionMatrixRat row column) column ()) row

/-- The stored last row and column are exactly the zero-sum lift of the section. -/
theorem gramMatrix_is_liftedSectionRat : gramMatrix = liftedSectionRat := by
  native_decide

end DH5GramLiftAudit
