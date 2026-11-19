module

public import Mathlib

/-! # Cauchy's theorem for finite groups

Prove Cauchy's theorem without Sylow theorems or an existing proof of Cauchy's theorem.
Use the action of the cyclic group of order `p` on tuples by cyclic rotation.
The tuple entries have ordered product one. This condition is preserved by rotation.
For positive `p`, count the tuples: there are `|G|^(p - 1)`.
The fixed tuples are constant. For prime `p`, the other orbits have size `p`.
Use the fixed points to find an element other than one whose `p`th power is one.
Useful declarations: `List.ofFn`, `List.prod`, `orderOf_eq_prime`, `ZMod`,
`AddAction.card_orbit_mul_card_stabilizer_eq_card_addGroup`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Quotient.html
-/

public section

noncomputable section
open Classical

namespace LeanSISSA.CauchyTheorem

/-- The `p`-tuples in `G` whose entries have ordered product one.
The list product uses the index order and does not assume that `G` is commutative. -/
abbrev ProductOneTuples (G : Type*) [Group G] (p : ℕ) : Type _ :=
  {x : Fin p → G // (List.ofFn x).prod = 1}

/-- If `G` is finite, the type of product-one tuples is finite. -/
noncomputable instance (G : Type*) [Group G] [Fintype G] (p : ℕ) :
    Fintype (ProductOneTuples G p) :=
  inferInstanceAs (Fintype {x : Fin p → G // (List.ofFn x).prod = 1})

/-- If `p` is positive, a product-one tuple is determined by its first `p - 1` entries. -/
theorem card_product_one_tuples (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : 0 < p) :
    Fintype.card (ProductOneTuples G p) = (Fintype.card G) ^ (p - 1) := by
  sorry

/-- Rotate a product-one tuple one position to the left. The index `i` of the result has
entry `x (i + 1)`, where addition of indices is modulo `p`. -/
def rotate {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (x : ProductOneTuples G p) : ProductOneTuples G p :=
  sorry

/-- If the tuple has length `p`, `p` rotations return the original tuple. -/
theorem rotate_iterate {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (x : ProductOneTuples G p) : (rotate p)^[p] x = x := by
  sorry

/-- The rotate action induces an action of the additive group `ZMod p` on product-one tuples. -/
def rotationAction {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (i : ZMod p) (t : ProductOneTuples G p) : ProductOneTuples G p :=
  sorry

/-- The additive group `ZMod p` acts on product-one tuples by repeated rotation. -/
instance {G : Type*} [Group G] (p : ℕ) [NeZero p] :
    AddAction (ZMod p) (ProductOneTuples G p) where
  vadd := sorry
  add_vadd := by sorry
  zero_vadd := by sorry

/-- In the rotation action, the element one performs one rotation.
The notation `+ᵥ` is for the additive group action. -/
theorem rotation_action_one {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (x : ProductOneTuples G p) :
    (1 : ZMod p) +ᵥ x = rotate p x := by
  sorry

/-- A product-one tuple is fixed by rotation if and only if it is constant.
Its constant entry `g` satisfies `g ^ p = 1`. -/
theorem rotate_fixed_iff {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (x : ProductOneTuples G p) :
    rotate p x = x ↔ ∃ g : G, g ^ p = 1 ∧ ∀ i, x.val i = g := by
  sorry

/-- For prime `p`, the number of product-one tuples and the number of fixed tuples are
congruent modulo `p`. Use the orbit decomposition for the rotation action. -/
theorem card_mod_fixed (G : Type*) [Group G] [Fintype G] (p : ℕ)
    [NeZero p] (hp : p.Prime) :
    Fintype.card (ProductOneTuples G p) % p =
      Nat.card {x : ProductOneTuples G p // rotate p x = x} % p := by
  sorry

/-- Let `p` be prime and divide the order of the finite group `G`.
Then `G` has an element of order `p`. -/
theorem exists_element_order_prime (G : Type*) [Group G] [Fintype G]
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Fintype.card G) :
    ∃ g : G, orderOf g = p := by
  sorry

/-- In a group, a product is one exactly when the second factor is the
inverse of the first. Hint: `mul_eq_one_iff_inv_eq` or cancellation. -/
theorem product_eq_one {G : Type*} [Group G] (g h : G) :
    g * h = 1 ↔ h = g⁻¹ := by
  sorry

/-- An element whose square is one equals its inverse.
Hint: rewrite `pow_two` and use `product_eq_one`. -/
theorem inverse_eq_of_square_eq_one {G : Type*} [Group G] (g : G)
    (hg : g ^ 2 = 1) : g⁻¹ = g := by
  sorry

/-- A product-one tuple of length one has its sole entry equal to one.
Hint: inspect `x.property`, then simplify `List.ofFn`. -/
theorem product_one_single_entry {G : Type*} [Group G]
    (x : ProductOneTuples G 1) : x.val 0 = 1 := by
  sorry

end LeanSISSA.CauchyTheorem
