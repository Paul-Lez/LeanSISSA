import Mathlib

/-! # The binomial theorem

This exercise states Newton's binomial formula in a commutative semiring.
Prove the formula by induction on `n`. Use Pascal's identity for the induction step.
Useful declarations: `Nat.choose_succ_succ`, `Finset.sum_range_succ`, `pow_succ`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Basic.html
-/

namespace LeanSISSA.BinomialTheorem

/-- For every natural number `n`, the `n`th power of a sum is the sum of the binomial terms. -/
theorem binomial_formula {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) :
    (a + b) ^ n = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : R) * a ^ k * b ^ (n - k) := by
  sorry

end LeanSISSA.BinomialTheorem
