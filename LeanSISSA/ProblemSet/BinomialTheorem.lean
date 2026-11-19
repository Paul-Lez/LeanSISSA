module

public import Mathlib

/-! # The binomial theorem

This exercise states Newton's binomial formula in a commutative semiring.
Prove the formula by induction on `n`. Use Pascal's identity for the induction step.
Useful declarations: `Nat.choose_succ_succ`, `Finset.sum_range_succ`, `pow_succ`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Choose/Basic.html
-/

public section

namespace LeanSISSA.BinomialTheorem

/-- The square of a sum in a commutative semiring.
Try to solve this without using the `ring` tactic. -/
theorem square_add {R : Type*} [CommSemiring R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  simp only [pow_two, add_mul, mul_add, two_mul]
  simp only [mul_comm, add_assoc, add_left_comm, add_comm]

/-- For every natural number `n`, the `n`th power of a sum is the sum of the binomial terms. -/
theorem binomial_formula {R : Type*} [CommSemiring R] (a b : R) (n : ℕ) :
    (a + b) ^ n = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : R) * a ^ k * b ^ (n - k) := by
  let t : ℕ → ℕ → R := fun n k => (Nat.choose n k : R) * a ^ k * b ^ (n - k)
  change (a + b) ^ n = ∑ k ∈ Finset.range (n + 1), t n k
  have hfirst (n : ℕ) : t n 0 = b ^ n := by
    simp [t]
  have hlast (n : ℕ) : t n (n + 1) = 0 := by
    simp [t]
  have hmiddle (n k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      t (n + 1) (k + 1) = a * t n k + b * t n (k + 1) := by
    have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    dsimp only [t]
    rw [Nat.choose_succ_succ, Nat.cast_add, add_mul]
    rw [pow_succ, Nat.succ_sub_succ]
    by_cases hk_eq : k = n
    · subst k
      simp [Nat.choose_succ_self]
      ring
    · have hk_lt : k < n := lt_of_le_of_ne hk_le hk_eq
      have hpow : n - k = n - (k + 1) + 1 := by omega
      rw [hpow, pow_succ]
      ring
  induction n with
  | zero =>
      rw [pow_zero, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
      simp [t]
  | succ n ih =>
      rw [Finset.sum_range_succ', hfirst, Finset.sum_congr rfl (hmiddle n),
        Finset.sum_add_distrib, add_assoc, _root_.pow_succ', ih, add_mul, Finset.mul_sum,
        Finset.mul_sum]
      congr 1
      rw [Finset.sum_range_succ', Finset.sum_range_succ, hfirst, hlast,
        mul_zero, add_zero, _root_.pow_succ']

end LeanSISSA.BinomialTheorem
