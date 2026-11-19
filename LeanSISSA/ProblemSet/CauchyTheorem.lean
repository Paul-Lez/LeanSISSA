module

/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning, Snir Broshi

The orbit-counting argument below is adapted from Mathlib.GroupTheory.PGroup.
-/
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
open MulAction
open scoped Fin.NatCast

namespace LeanSISSA.CauchyTheorem

/-- The `p`-tuples in `G` whose entries have ordered product one.
The list product uses the index order and does not assume that `G` is commutative. -/
abbrev ProductOneTuples (G : Type*) [Group G] (p : ℕ) : Type _ :=
  {x : Fin p → G // (List.ofFn x).prod = 1}

/-- If `G` is finite, the type of product-one tuples is finite. -/
noncomputable instance (G : Type*) [Group G] [Fintype G] (p : ℕ) :
    Fintype (ProductOneTuples G p) := by
  classical
  unfold ProductOneTuples
  infer_instance

/-- If `p` is positive, a product-one tuple is determined by its first `p - 1` entries. -/
theorem card_product_one_tuples (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : 0 < p) :
    Fintype.card (ProductOneTuples G p) = (Fintype.card G) ^ (p - 1) := by
  classical
  cases p with
  | zero => omega
  | succ n =>
    let e : ProductOneTuples G (n + 1) ≃ (Fin n → G) := {
      toFun x := Fin.init x.1
      invFun f := ⟨Fin.snoc f ((List.ofFn f).prod)⁻¹, by
        rw [List.ofFn_succ']
        simp [Fin.snoc_castSucc, Fin.snoc_last]
      ⟩
      left_inv x := by
        apply Subtype.ext
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [Fin.snoc_last]
          have hx := x.2
          rw [List.ofFn_succ'] at hx
          rw [List.prod_concat] at hx
          rw [Fin.init_def]
          simpa using (mul_eq_one_iff_inv_eq.mp hx)
        · simp [Fin.init_def]
      right_inv f := by
        funext i
        simp
    }
    rw [Fintype.card_congr e, Fintype.card_fun]
    simp

/-- Rotate a product-one tuple one position to the left. The index `i` of the result has
entry `x (i + 1)`, where addition of indices is modulo `p`. -/
def rotate {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (x : ProductOneTuples G p) : ProductOneTuples G p := by
  cases p with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    refine ⟨Fin.snoc (Fin.tail x.val) (x.val 0), ?_⟩
    have hx := x.property
    rw [List.ofFn_succ, List.prod_cons] at hx
    rw [List.ofFn_succ_last]
    simpa only [Fin.snoc_castSucc, Fin.snoc_last, Fin.tail, List.prod_append,
      List.prod_singleton] using (mul_eq_one_comm.mp hx)

lemma rotate_apply {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (x : ProductOneTuples G p) (i : Fin p) :
    (rotate p x).val i = x.val (i + 1) := by
  cases p with
  | zero => exact Fin.elim0 i
  | succ n =>
    induction i using Fin.lastCases with
    | last => simp [rotate]
    | cast i =>
      simp only [rotate, Fin.snoc_castSucc, Fin.tail]
      apply congrArg x.val
      apply Fin.ext
      simp [Fin.add_def]
      exact (Nat.mod_eq_of_lt (Nat.succ_lt_succ i.isLt)).symm

lemma rotate_iterate_apply {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (m : ℕ) (x : ProductOneTuples G p) (i : Fin p) :
    ((rotate p)^[m] x).val i = x.val (i + (↑m : Fin p)) := by
  induction m generalizing i with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', rotate_apply, ih]
    simp [Nat.cast_add, add_comm, add_left_comm]

/-- If the tuple has length `p`, `p` rotations return the original tuple. -/
theorem rotate_iterate {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (x : ProductOneTuples G p) : (rotate p)^[p] x = x := by
  apply Subtype.ext
  funext i
  rw [rotate_iterate_apply]
  simp

/-- The rotate action induces an action of the additive group `ZMod p` on product-one tuples. -/
def rotationAction {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (i : ZMod p) (t : ProductOneTuples G p) : ProductOneTuples G p :=
  (rotate p)^[i.val] t

/-- The additive group `ZMod p` acts on product-one tuples by repeated rotation. -/
instance {G : Type*} [Group G] (p : ℕ) [NeZero p] :
    AddAction (ZMod p) (ProductOneTuples G p) where
  vadd := rotationAction p
  zero_vadd x := by
    change (rotate p)^[(0 : ZMod p).val] x = x
    simp
  add_vadd g h x := by
    change (rotate p)^[(g + h).val] x = (rotate p)^[g.val] ((rotate p)^[h.val] x)
    simp only [ZMod.val_add]
    rw [Function.IsPeriodicPt.iterate_mod_apply
      (show Function.IsPeriodicPt (rotate p) p x from rotate_iterate p x)
      (g.val + h.val)]
    rw [← Function.iterate_add_apply]

/-- In the rotation action, the element one performs one rotation. -/
theorem rotation_action_one {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (x : ProductOneTuples G p) :
    (1 : ZMod p) +ᵥ x = rotate p x := by
  change (rotate p)^[(1 : ZMod p).val] x = rotate p x
  simp only [ZMod.val_one_eq_one_mod]
  rw [(show Function.IsPeriodicPt (rotate p) p x from rotate_iterate p x).iterate_mod_apply 1]
  simp

/-- A product-one tuple is fixed by rotation if and only if it is constant.
Its constant entry `g` satisfies `g ^ p = 1`. -/
theorem rotate_fixed_iff {G : Type*} [Group G] (p : ℕ) [NeZero p]
    (x : ProductOneTuples G p) :
    rotate p x = x ↔ ∃ g : G, g ^ p = 1 ∧ ∀ i, x.val i = g := by
  constructor
  · intro h
    have hconst : ∀ i, x.val i = x.val 0 := by
      intro i
      have hcoord := rotate_iterate_apply p i.val x 0
      have hi : (↑i.val : Fin p) = i := Fin.ext (by simp)
      rw [hi] at hcoord
      have hiter : ((rotate p)^[i.val] x) = x := by simp [Function.iterate_fixed h]
      rw [hiter] at hcoord
      simpa [Fin.zero_add] using hcoord.symm
    refine ⟨x.val 0, ?_, hconst⟩
    have hx := x.property
    have hfun : x.val = fun _ => x.val 0 := funext hconst
    rw [hfun, List.ofFn_const] at hx
    simpa [List.prod_replicate] using hx
  · rintro ⟨g, _, hconst⟩
    apply Subtype.ext
    funext i
    rw [rotate_apply, hconst, hconst]

private theorem rotation_generator_fixed_iff {p : ℕ} [Fact p.Prime]
    {α : Type*} [AddAction (ZMod p) α] (x : α) :
    (1 : ZMod p) +ᵥ x = x ↔ x ∈ MulAction.fixedPoints (Multiplicative (ZMod p)) α := by
  letI : MulAction (Multiplicative (ZMod p)) α := inferInstance
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro hx g
    have hn (n : ℕ) : (n • (1 : ZMod p)) +ᵥ x = x := by
      induction n with
      | zero => simp
      | succ n ih => rw [succ_nsmul, add_vadd, hx, ih]
    change g.toAdd +ᵥ x = x
    simpa [nsmul_eq_mul] using hn g.toAdd.val
  · intro hx
    have := hx (Multiplicative.ofAdd (1 : ZMod p))
    simpa using this

private theorem card_mod_generator_fixed {p : ℕ} [Fact p.Prime]
    {α : Type*} [AddAction (ZMod p) α] [Finite α] :
    Nat.card α % p = Nat.card {x : α // (1 : ZMod p) +ᵥ x = x} % p := by
  classical
  letI : MulAction (Multiplicative (ZMod p)) α := inferInstance
  let G := Multiplicative (ZMod p)
  haveI : Fintype α := Fintype.ofFinite α
  haveI : Fintype G := Fintype.ofFinite G
  have hGcard : Fintype.card G = p := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  -- Orbit-stabilizer makes every orbit size a divisor of the prime p.
  have hOrbitDvd : ∀ b : α, Fintype.card (orbit G b) ∣ p := by
    intro b
    haveI : Fintype (stabilizer G b) := Fintype.ofFinite _
    have h := card_orbit_mul_card_stabilizer_eq_card_group G b
    have h' : Fintype.card (orbit G b) * Fintype.card (stabilizer G b) = p := by
      calc
        _ = Fintype.card G := h
        _ = p := hGcard
    exact ⟨Fintype.card (stabilizer G b), h'.symm⟩
  have hequiv :
      {x : α // x ∈ MulAction.fixedPoints G α} ≃
        {x : α // (1 : ZMod p) +ᵥ x = x} :=
    Equiv.subtypeEquiv (Equiv.refl α) (fun x => (rotation_generator_fixed_iff x).symm)
  have hcardEq : Nat.card {x : α // x ∈ MulAction.fixedPoints G α} =
      Nat.card {x : α // (1 : ZMod p) +ᵥ x = x} := Nat.card_congr hequiv
  haveI : Fintype (MulAction.fixedPoints G α) := Fintype.ofFinite _
  haveI : Fintype {x : α // (1 : ZMod p) +ᵥ x = x} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, ← hcardEq, Nat.card_eq_fintype_card]
  -- Partition into orbits. Modulo p, only singleton orbits contribute.
  calc
    Fintype.card α = Fintype.card (Σ y : Quotient (orbitRel G α),
        {x // Quotient.mk'' x = y}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbitRel G α))).symm
    _ = ∑ a : Quotient (orbitRel G α), Fintype.card {x // Quotient.mk'' x = a} :=
      Fintype.card_sigma
    _ ≡ ∑ _a : MulAction.fixedPoints G α, 1 [MOD p] := by
      rw [← ZMod.natCast_eq_natCast_iff _ _ p, Nat.cast_sum, Nat.cast_sum]
      have key : ∀ x,
          Fintype.card {y // (Quotient.mk'' y : Quotient (orbitRel G α)) = Quotient.mk'' x} =
            Fintype.card (orbit G x) := by
        intro x
        simp only [Quotient.eq'']
        congr
      refine Eq.symm (Finset.sum_bij_ne_zero
        (fun a _ _ => Quotient.mk'' a.1)
        (fun _ _ _ => Finset.mem_univ _)
        (fun a₁ _ _ a₂ _ _ h =>
          Subtype.ext (mem_fixedPoints'.mp a₂.2 a₁.1 (Quotient.exact' h)))
        (fun b => Quotient.inductionOn' b fun b _ hb => ?_)
        (fun a _ _ => by rw [key, mem_fixedPoints_iff_card_orbit_eq_one.mp a.2]))
      have hdiv := hOrbitDvd b
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with hord | hord
      · have hfix : b ∈ MulAction.fixedPoints G α :=
          mem_fixedPoints_iff_card_orbit_eq_one.mpr hord
        exact ⟨⟨b, hfix⟩, Finset.mem_univ _, by simp, rfl⟩
      · exfalso
        apply hb
        rw [key b, hord]
        simp
    _ = Fintype.card (MulAction.fixedPoints G α) := by simp

/-- For prime `p`, the number of product-one tuples and the number of fixed tuples are
congruent modulo `p`. Use the orbit decomposition for the rotation action. -/
theorem card_mod_fixed (G : Type*) [Group G] [Fintype G] (p : ℕ)
    [NeZero p] (hp : p.Prime) :
    Fintype.card (ProductOneTuples G p) % p =
      Nat.card {x : ProductOneTuples G p // rotate p x = x} % p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have e : {x : ProductOneTuples G p // (1 : ZMod p) +ᵥ x = x} ≃
      {x : ProductOneTuples G p // rotate p x = x} := by
    refine Equiv.subtypeEquiv (Equiv.refl _) ?_
    intro x
    change ((1 : ZMod p) +ᵥ x = x) ↔ rotate p x = x
    rw [rotation_action_one]
  have h := card_mod_generator_fixed (p := p) (α := ProductOneTuples G p)
  rw [Nat.card_eq_fintype_card] at h
  rw [Nat.card_congr e] at h
  exact h

/-- Let `p` be prime and divide the order of the finite group `G`.
Then `G` has an element of order `p`. -/
theorem exists_element_order_prime (G : Type*) [Group G] [Fintype G]
    (p : ℕ) (hp : p.Prime) (hdiv : p ∣ Fintype.card G) :
    ∃ g : G, orderOf g = p := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  let oneTuple : ProductOneTuples G p := ⟨fun _ => 1, by simp⟩
  have hcard : p ∣ Fintype.card (ProductOneTuples G p) := by
    rw [card_product_one_tuples G p hp.pos]
    exact dvd_pow hdiv (by omega)
  have hfixed : p ∣ Nat.card {x : ProductOneTuples G p // rotate p x = x} := by
    apply Nat.dvd_of_mod_eq_zero
    rw [← card_mod_fixed G p hp]
    exact Nat.mod_eq_zero_of_dvd hcard
  have hex : ∃ x : {x : ProductOneTuples G p // rotate p x = x}, x.1 ≠ oneTuple := by
    by_contra h
    push_neg at h
    have hone : Fintype.card {x : ProductOneTuples G p // rotate p x = x} = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      refine ⟨⟨oneTuple, ?_⟩, ?_⟩
      · exact (rotate_fixed_iff p oneTuple).2 ⟨1, by simp, fun _ => rfl⟩
      · intro y
        apply Subtype.ext
        exact h y
    have : p ∣ 1 := by simpa [hone] using hfixed
    exact hp.not_dvd_one this
  obtain ⟨x, hx⟩ := hex
  obtain ⟨g, hgp, hconst⟩ := (rotate_fixed_iff p x.1).mp x.2
  refine ⟨g, orderOf_eq_prime hgp ?_⟩
  intro hg
  apply hx
  apply Subtype.ext
  funext i
  rw [hconst i, hg]

/-- In a group, a product is one exactly when the second factor is the
inverse of the first. Hint: `mul_eq_one_iff_inv_eq` or cancellation. -/
theorem product_eq_one {G : Type*} [Group G] (g h : G) :
    g * h = 1 ↔ h = g⁻¹ := by
  constructor
  · intro hprod
    exact (mul_eq_one_iff_inv_eq.mp hprod).symm
  · intro hh
    rw [hh, mul_inv_cancel]

/-- An element whose square is one equals its inverse.
Hint: rewrite `pow_two` and use `product_eq_one`. -/
theorem inverse_eq_of_square_eq_one {G : Type*} [Group G] (g : G)
    (hg : g ^ 2 = 1) : g⁻¹ = g := by
  exact ((product_eq_one g g).mp (by simpa [pow_two] using hg)).symm

/-- A product-one tuple of length one has its sole entry equal to one.
Hint: inspect `x.property`, then simplify `List.ofFn`. -/
theorem product_one_single_entry {G : Type*} [Group G]
    (x : ProductOneTuples G 1) : x.val 0 = 1 := by
  have h := x.property
  simpa [List.ofFn_succ] using h


end LeanSISSA.CauchyTheorem
