module

public import Mathlib

/-! Every positive integer is a sum of distinct Fibonacci numbers. -/

public section

/-- Every positive integer can be written as a sum of distinct Fibonacci numbers. -/
theorem zeckendorf_existence (n : ℕ) (hn : 0 < n) :
    ∃ s : Finset ℕ, s.sum Nat.fib = n := by
  -- You can argue by strong induction on `n`.
  sorry


/- Mini challenge: one can also prove a uniqueness result on this (see https://en.wikipedia.org/wiki/Zeckendorf%27s_theorem).
State and prove this! -/
