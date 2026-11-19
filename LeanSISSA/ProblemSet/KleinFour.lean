module

public import Mathlib

/-! # The Klein four group

The Klein four group has four elements: the identity `e` and three nonidentity elements
`a`, `b`, and `c`. Each nonidentity element squared is `e`, and the product of two
distinct nonidentity elements is the third. The multiplication table is defined below.

Replace each `sorry` with a proof. For statements about arbitrary elements, `cases` can
split into the four possible cases; `rfl` can then evaluate the multiplication table.
The last exercises use the group structure assembled from the earlier results.
-/

public section

namespace LeanSISSA.KleinFour

/-- The four elements of the Klein four group. -/
public inductive Klein where
  | e | a | b | c
  deriving DecidableEq, Inhabited

open Klein

-- TODO(Paul): we should be able to auto-derive the `Fintype` instance here but there's a bug.
instance : Fintype Klein where
  elems := {e, a, b, c}
  complete := by
    intro x
    match x with
    | e => grind
    | a => grind
    | b => grind
    | c => grind

/-- The multiplication table for the Klein four group. -/
def mul : Klein → Klein → Klein
  | e, x => x
  | a, e => a
  | a, a => e
  | a, b => c
  | a, c => b
  | b, e => b
  | b, a => c
  | b, b => e
  | b, c => a
  | c, e => c
  | c, a => b
  | c, b => a
  | c, c => e

instance : Mul Klein := ⟨mul⟩

/-- Compute a product directly from the table. -/
theorem a_mul_b : a * b = c := by
  sorry

/-- The identity acts on the left. -/
theorem e_mul (x : Klein) : e * x = x := by
  sorry

/-- The identity acts on the right. -/
theorem mul_e (x : Klein) : x * e = x := by
  sorry

/-- Every element is its own inverse. -/
theorem mul_self (x : Klein) : x * x = e := by
  sorry

/-- Multiplication is commutative. -/
theorem mul_comm (x y : Klein) : x * y = y * x := by
  sorry

/-- Multiplication is associative. Hint: split into cases on all three elements. -/
theorem mul_assoc (x y z : Klein) : (x * y) * z = x * (y * z) := by
  sorry

/-- The preceding exercises give the Klein four group its commutative group structure. -/
instance : CommGroup Klein where
  mul := mul
  mul_assoc := mul_assoc
  one := e
  one_mul := e_mul
  mul_one := mul_e
  inv := id
  inv_mul_cancel := mul_self
  mul_comm := mul_comm

/-- In group notation, every element is its own inverse. -/
theorem inv_eq_self (x : Klein) : x⁻¹ = x := by
  sorry

/-- Every element has square one. -/
theorem square_eq_one (x : Klein) : x ^ 2 = 1 := by
  sorry

/-- Multiplying twice by the same element returns the original element.
Hint: use associativity and `square_eq_one` or `mul_self`. -/
theorem mul_mul_self (x y : Klein) : x * (x * y) = y := by
  sorry

/-- Solve an equation in the Klein four group. Hint: use the previous exercise. -/
theorem solve_mul (x y z : Klein) (h : x * y = z) : y = x * z := by
  sorry

end LeanSISSA.KleinFour
