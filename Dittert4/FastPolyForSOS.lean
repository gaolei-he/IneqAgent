import Dittert4.SparsePolyCheck

namespace FastPolyForSOS

open SparsePolyCheck

abbrev MapPoly := Std.TreeMap Nat ℚ

def base : Nat := 9

def encode {n : Nat} (exponent : Exp n) : Nat :=
  (List.ofFn exponent).foldl (fun key power => key * base + power) 0

def decode (n key : Nat) : Exp n :=
  fun index => (key / (base ^ (n - 1 - index.val))) % base

def accumulate (map : MapPoly) (key : Nat) (coefficient : ℚ) : MapPoly :=
  map.alter key fun old =>
    let result := old.getD 0 + coefficient
    if result = 0 then none else some result

def ofPoly {n : Nat} (poly : Poly n) : MapPoly :=
  poly.foldl
    (fun result term => accumulate result (encode term.exp) term.coeff)
    {}

def insertAll (source target : MapPoly) : MapPoly :=
  source.foldl
    (fun result key coefficient => accumulate result key coefficient)
    target

def addMap (left right : MapPoly) : MapPoly :=
  if left.size ≤ right.size then
    insertAll left right
  else
    insertAll right left

def addManyMap (polys : List MapPoly) : MapPoly :=
  polys.foldl addMap {}

def addProduct (map : MapPoly) (leftKey : Nat) (leftCoefficient : ℚ)
    (rightKey : Nat) (rightCoefficient : ℚ) (factor : ℚ := 1) : MapPoly :=
  accumulate map (leftKey + rightKey)
    (factor * leftCoefficient * rightCoefficient)

def multiplyInto (left right : MapPoly) : MapPoly :=
  left.foldl
    (fun result leftKey leftCoefficient =>
      right.foldl
        (fun result rightKey rightCoefficient =>
          addProduct result leftKey leftCoefficient rightKey rightCoefficient)
        result)
    {}

def mulMap (left right : MapPoly) : MapPoly :=
  if left.size ≤ right.size then
    multiplyInto left right
  else
    multiplyInto right left

def squareMapAux : List (Nat × ℚ) → MapPoly → MapPoly
  | [], result => result
  | (key, coefficient) :: tail, result =>
      let result := addProduct result key coefficient key coefficient
      let result := tail.foldl
        (fun result term =>
          addProduct result key coefficient term.1 term.2 2)
        result
      squareMapAux tail result

def squareMap (poly : MapPoly) : MapPoly :=
  squareMapAux poly.toList {}

def toPoly (n : Nat) (map : MapPoly) : Poly n :=
  map.toList.map fun (key, coefficient) =>
    { exp := decode n key, coeff := coefficient }

def add {n : Nat} (left right : Poly n) : Poly n :=
  toPoly n (addMap (ofPoly left) (ofPoly right))

def addMany {n : Nat} (polys : List (Poly n)) : Poly n :=
  toPoly n (polys.foldl (fun result poly => addMap result (ofPoly poly)) {})

def mul {n : Nat} (left right : Poly n) : Poly n :=
  toPoly n (mulMap (ofPoly left) (ofPoly right))

def square {n : Nat} (poly : Poly n) : Poly n :=
  toPoly n (squareMap (ofPoly poly))

def fastNormalizeImpl {n : Nat} (poly : Poly n) : Poly n :=
  toPoly n (ofPoly poly)

@[implemented_by fastNormalizeImpl] def fastNormalize {n : Nat} (poly : Poly n) : Poly n :=
  normalize poly

@[simp] theorem eval_fastNormalize {n : Nat} (x : Fin n → ℝ) (poly : Poly n) :
    eval x (fastNormalize poly) = eval x poly := by
  simp [fastNormalize]

end FastPolyForSOS
