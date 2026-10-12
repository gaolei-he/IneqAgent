import Dittert5.DH5Coefficient

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace DH5OrbitSum

open scoped BigOperators
open DH5GramData DH5Symmetry DH5Coefficient

/-- The identity row/column operation, with no transpose. -/
def identityTransform : Transform :=
  ⟨Equiv.refl Side, Equiv.refl Side, false⟩

@[simp] theorem compose_identity_left (transformation : Transform) :
    compose identityTransform transformation = transformation := by
  rcases transformation with ⟨rowPermutation, columnPermutation, transposed⟩
  cases transposed <;> simp [compose, identityTransform]

@[simp] theorem compose_identity_right (transformation : Transform) :
    compose transformation identityTransform = transformation := by
  rcases transformation with ⟨rowPermutation, columnPermutation, transposed⟩
  cases transposed <;> simp [compose, identityTransform]

theorem compose_associative (outer middle inner : Transform) :
    compose outer (compose middle inner) =
      compose (compose outer middle) inner := by
  rcases outer with ⟨outerRow, outerColumn, outerTranspose⟩
  rcases middle with ⟨middleRow, middleColumn, middleTranspose⟩
  rcases inner with ⟨innerRow, innerColumn, innerTranspose⟩
  cases outerTranspose <;> cases middleTranspose <;> cases innerTranspose <;>
    simp [compose, Equiv.trans_assoc]

@[simp] theorem compose_inverse_right (transformation : Transform) :
    compose transformation (inverse transformation) = identityTransform := by
  rcases transformation with ⟨rowPermutation, columnPermutation, transposed⟩
  cases transposed <;> simp [compose, inverse, identityTransform]

@[simp] theorem compose_inverse_left (transformation : Transform) :
    compose (inverse transformation) transformation = identityTransform := by
  rcases transformation with ⟨rowPermutation, columnPermutation, transposed⟩
  cases transposed <;> simp [compose, inverse, identityTransform]

/-- Right composition by a fixed operation only reorders the 28,800 operations. -/
def rightComposeEquiv (inner : Transform) : Transform ≃ Transform where
  toFun outer := compose outer inner
  invFun outer := compose outer (inverse inner)
  left_inv outer := by
    change compose (compose outer inner) (inverse inner) = outer
    rw [← compose_associative, compose_inverse_right, compose_identity_right]
  right_inv outer := by
    change compose (compose outer (inverse inner)) inner = outer
    rw [← compose_associative, compose_inverse_left, compose_identity_right]

/-- Left composition by a fixed operation only reorders the 28,800 operations. -/
def leftComposeEquiv (outer : Transform) : Transform ≃ Transform where
  toFun inner := compose outer inner
  invFun inner := compose (inverse outer) inner
  left_inv inner := by
    change compose (inverse outer) (compose outer inner) = inner
    rw [compose_associative, compose_inverse_left, compose_identity_left]
  right_inv inner := by
    change compose outer (compose (inverse outer) inner) = inner
    rw [compose_associative, compose_inverse_right, compose_identity_left]

/-- An unordered product of exactly five matrix entries. -/
abbrev DegreeFiveMonomial := Sym Cell 5

/-- Forget the order in which the five factors were written. -/
def monomialOfFactors (factors : Factors) : DegreeFiveMonomial :=
  Sym.mk (List.ofFn factors) (by simp)

/-- Decode one stored base-25 monomial key as an unordered five-factor product. -/
def monomialOfKey (key : Nat) : DegreeFiveMonomial :=
  monomialOfFactors (factorsOfKey key)

/-- Apply a row/column operation to every factor of an unordered monomial. -/
def actMonomial (transformation : Transform)
    (monomial : DegreeFiveMonomial) : DegreeFiveMonomial :=
  Sym.map (actCell transformation) monomial

@[simp] theorem actMonomial_compose (outer inner : Transform)
    (monomial : DegreeFiveMonomial) :
    actMonomial (compose outer inner) monomial =
      actMonomial outer (actMonomial inner monomial) := by
  unfold actMonomial
  rw [Sym.map_map]
  apply Sym.map_congr
  intro cell _
  exact actCell_compose outer inner cell

@[simp] theorem actMonomial_identity (monomial : DegreeFiveMonomial) :
    actMonomial identityTransform monomial = monomial := by
  unfold actMonomial
  rw [show actCell identityTransform = id by
    funext cell
    rcases cell with ⟨row, column⟩
    simp [actCell, identityTransform]]
  exact Sym.map_id monomial

@[simp] theorem actMonomial_inverse_left (transformation : Transform)
    (monomial : DegreeFiveMonomial) :
    actMonomial (inverse transformation)
      (actMonomial transformation monomial) = monomial := by
  rw [← actMonomial_compose, compose_inverse_left, actMonomial_identity]

@[simp] theorem actMonomial_inverse_right (transformation : Transform)
    (monomial : DegreeFiveMonomial) :
    actMonomial transformation
      (actMonomial (inverse transformation) monomial) = monomial := by
  rw [← actMonomial_compose, compose_inverse_right, actMonomial_identity]

def representativeMonomial (classId : Fin classCount) : DegreeFiveMonomial :=
  monomialOfKey (representativeKey classId)

/-- The stored orbit, now interpreted as actual unordered degree-five monomials. -/
def storedOrbit (classId : Fin classCount) : Finset DegreeFiveMonomial :=
  ((orbitList classId).map monomialOfKey).toFinset

def decodedCanonicalKey (key : Nat) : Nat :=
  let digits := (List.ofFn fun index : Fin 5 => keyDigit key index).mergeSort
    (fun left right => decide (left ≤ right))
  digits.foldl (fun code digit => 25 * code + digit) 0

def adjacentStrictlyIncreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      first < second && adjacentStrictlyIncreasing (second :: rest)

def decodedMonomialsNodupImpl (keys : List Nat) : Bool :=
  let codes := (keys.map decodedCanonicalKey).mergeSort
    (fun left right => decide (left ≤ right))
  adjacentStrictlyIncreasing codes

@[implemented_by decodedMonomialsNodupImpl]
def decodedMonomialsNodup (keys : List Nat) : Bool :=
  decide ((keys.map monomialOfKey).Nodup)

/-- Decoding the stored keys introduces no duplicate monomials in any orbit. -/
theorem decoded_orbit_lists_nodup_audit :
    ∀ classId : Fin classCount,
      decodedMonomialsNodup (orbitList classId) = true := by
  native_decide

theorem orbit_monomial_lists_nodup (classId : Fin classCount) :
    ((orbitList classId).map monomialOfKey).Nodup := by
  apply of_decide_eq_true
  change decide (((orbitList classId).map monomialOfKey).Nodup) = true
  change decodedMonomialsNodup (orbitList classId) = true
  exact decoded_orbit_lists_nodup_audit classId

/-- The image of all 28,800 operations applied to one monomial. -/
def actionImage (monomial : DegreeFiveMonomial) : Finset DegreeFiveMonomial :=
  Finset.univ.image (fun transformation : Transform =>
    actMonomial transformation monomial)

/-- The exported orbit slices are exactly the images of the 28,800 allowed operations. -/
theorem storedOrbit_eq_actionImage :
    ∀ classId : Fin classCount,
      storedOrbit classId = actionImage (representativeMonomial classId) := by
  native_decide

/-- Operations carrying `base` to `target`. -/
def actionFiber (base target : DegreeFiveMonomial) : Finset Transform :=
  Finset.univ.filter fun transformation =>
    actMonomial transformation base = target

/-- Operations fixing one monomial. -/
def monomialStabilizer (monomial : DegreeFiveMonomial) : Finset Transform :=
  actionFiber monomial monomial

/-- Left composition identifies the stabilizer with every nonempty action fiber. -/
def stabilizerEquivFiber (base : DegreeFiveMonomial) (outer : Transform) :
    {transformation // transformation ∈ monomialStabilizer base} ≃
      {transformation // transformation ∈
        actionFiber base (actMonomial outer base)} where
  toFun transformation := ⟨compose outer transformation.1, by
    have fixed : actMonomial transformation.1 base = base := by
      exact (Finset.mem_filter.mp transformation.2).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [actMonomial_compose, fixed]⟩
  invFun transformation := ⟨compose (inverse outer) transformation.1, by
    have reaches : actMonomial transformation.1 base = actMonomial outer base := by
      exact (Finset.mem_filter.mp transformation.2).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [actMonomial_compose, reaches, actMonomial_inverse_left]⟩
  left_inv transformation := by
    apply Subtype.ext
    change compose (inverse outer) (compose outer transformation.1) =
      transformation.1
    rw [compose_associative, compose_inverse_left, compose_identity_left]
  right_inv transformation := by
    apply Subtype.ext
    change compose outer (compose (inverse outer) transformation.1) =
      transformation.1
    rw [compose_associative, compose_inverse_right, compose_identity_left]

theorem actionFiber_card_eq_stabilizer (base : DegreeFiveMonomial)
    (outer : Transform) :
    (actionFiber base (actMonomial outer base)).card =
      (monomialStabilizer base).card := by
  simpa using Fintype.card_congr (stabilizerEquivFiber base outer).symm

theorem actionFiber_card_of_mem_actionImage (base target : DegreeFiveMonomial)
    (membership : target ∈ actionImage base) :
    (actionFiber base target).card = (monomialStabilizer base).card := by
  rcases Finset.mem_image.mp membership with
    ⟨transformation, _, equality⟩
  subst target
  exact actionFiber_card_eq_stabilizer base transformation

/--
Fiberwise summation: summing a weight over all operations is the stabilizer
size times one copy of every distinct monomial in the orbit.
-/
theorem sum_action_eq_stabilizer_nsmul_orbit
    {R : Type} [AddCommMonoid R]
    (base : DegreeFiveMonomial) (weight : DegreeFiveMonomial → R) :
    (∑ transformation : Transform,
        weight (actMonomial transformation base)) =
      (monomialStabilizer base).card •
        (∑ monomial ∈ actionImage base, weight monomial) := by
  calc
    (∑ transformation : Transform,
        weight (actMonomial transformation base)) =
        ∑ monomial ∈ actionImage base,
          ∑ transformation ∈ actionFiber base monomial,
            weight (actMonomial transformation base) := by
      symm
      simpa [actionFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset Transform))
          (t := actionImage base)
          (g := fun transformation => actMonomial transformation base)
          (f := fun transformation =>
            weight (actMonomial transformation base))
          (fun transformation _ =>
            Finset.mem_image.mpr ⟨transformation, Finset.mem_univ _, rfl⟩))
    _ = ∑ monomial ∈ actionImage base,
          (monomialStabilizer base).card • weight monomial := by
      apply Finset.sum_congr rfl
      intro monomial membership
      rw [← actionFiber_card_of_mem_actionImage base monomial membership]
      rw [← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro transformation transformationMembership
      have equality : actMonomial transformation base = monomial := by
        simpa [actionFiber] using transformationMembership
      rw [equality]
    _ = (monomialStabilizer base).card •
          (∑ monomial ∈ actionImage base, weight monomial) := by
      exact Finset.sum_nsmul _ _ _

/-- The stabilizer sizes stored in the certificate are exact. -/
theorem exact_monomial_stabilizer_counts :
    ∀ classId : Fin classCount,
      (monomialStabilizer (representativeMonomial classId)).card =
        classRepetition classId := by
  native_decide

/-- The abstract 54-orbit sum is exactly the genuine 28,800-operation sum. -/
theorem representative_transform_sum_compressed
    {R : Type} [AddCommMonoid R]
    (classId : Fin classCount) (weight : DegreeFiveMonomial → R) :
    (∑ transformation : Transform,
        weight (actMonomial transformation
          (representativeMonomial classId))) =
      classRepetition classId •
        (∑ monomial ∈ storedOrbit classId, weight monomial) := by
  rw [storedOrbit_eq_actionImage]
  rw [← exact_monomial_stabilizer_counts classId]
  exact sum_action_eq_stabilizer_nsmul_orbit
    (representativeMonomial classId) weight

/-- Every Gram monomial key is genuinely present in its declared stored orbit. -/
theorem gram_keys_mem_orbit_lists :
    ∀ position : Fin 52975,
      gramMonomialKey position.val ∈
        orbitList (gramClassId position.val) := by
  native_decide

theorem gram_monomial_mem_storedOrbit (position : Fin 52975) :
    monomialOfKey (gramMonomialKey position.val) ∈
      storedOrbit (gramClassId position.val) := by
  unfold storedOrbit
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨gramMonomialKey position.val,
    gram_keys_mem_orbit_lists position, rfl⟩

/--
If a monomial lies in a stored orbit, right composition shows that its
28,800 transformed copies have the same sum as the chosen representative.
-/
theorem orbit_point_transform_sum_compressed
    {R : Type} [AddCommMonoid R]
    (classId : Fin classCount) (point : DegreeFiveMonomial)
    (membership : point ∈ storedOrbit classId)
    (weight : DegreeFiveMonomial → R) :
    (∑ transformation : Transform,
        weight (actMonomial transformation point)) =
      classRepetition classId •
        (∑ monomial ∈ storedOrbit classId, weight monomial) := by
  have imageMembership :
      point ∈ actionImage (representativeMonomial classId) := by
    rw [← storedOrbit_eq_actionImage]
    exact membership
  rcases Finset.mem_image.mp imageMembership with
    ⟨inner, _, pointEquality⟩
  calc
    (∑ transformation : Transform,
        weight (actMonomial transformation point)) =
        ∑ transformation : Transform,
          weight (actMonomial (compose transformation inner)
            (representativeMonomial classId)) := by
      apply Finset.sum_congr rfl
      intro transformation _
      rw [← pointEquality, ← actMonomial_compose]
    _ = ∑ transformation : Transform,
          weight (actMonomial transformation
            (representativeMonomial classId)) := by
      exact Equiv.sum_comp (rightComposeEquiv inner)
        (fun transformation => weight (actMonomial transformation
          (representativeMonomial classId)))
    _ = classRepetition classId •
          (∑ monomial ∈ storedOrbit classId, weight monomial) :=
      representative_transform_sum_compressed classId weight

/-- The compression theorem specialized to every upper-triangular Gram entry. -/
theorem gram_entry_transform_sum_compressed
    {R : Type} [AddCommMonoid R]
    (position : Fin 52975) (weight : DegreeFiveMonomial → R) :
    (∑ transformation : Transform,
        weight (actMonomial transformation
          (monomialOfKey (gramMonomialKey position.val)))) =
      classRepetition (gramClassId position.val) •
        (∑ monomial ∈ storedOrbit (gramClassId position.val),
          weight monomial) :=
  orbit_point_transform_sum_compressed
    (gramClassId position.val)
    (monomialOfKey (gramMonomialKey position.val))
    (gram_monomial_mem_storedOrbit position) weight

end DH5OrbitSum
