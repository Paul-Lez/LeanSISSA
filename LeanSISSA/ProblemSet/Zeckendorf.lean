import Mathlib

/-! The Zeckendorf representation of a positive integer is a unique way
of writing it as a sum of distinct Fibonacci numbers. -/

/-- Every positive integer can be written as a sum of distinct Fibonacci numbers. -/
theorem zeckendorf (n : ℕ) (hn : 0 < n) :
    ∃ s : Finset ℕ, s.sum Nat.fib = n := by
  sorry
