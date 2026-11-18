module

public import Mathlib

/-! # A small demo file

This file contains a few basic demos to show how Lean works
-/

public section




































/- The basic syntax and tactics. -/

/-- Triangular numbers are numbers of the form ∑_{i ≤ 0}^n i. -/
def TriangularNumber (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, i

theorem triangularNumber_succ : ∀ n, TriangularNumber (n + 1) = TriangularNumber n + (n + 1) := by
  -- Finset.sum_Icc_succ_top, Nat.le_add_left
  sorry

theorem triangularNumber_zero : TriangularNumber 0 = 0 := by
  -- Finset.Icc_eq_empty, Finset.sum_empty
  sorry


theorem exists_triangularNumber_eq : ∃ n, TriangularNumber n = 6 := by
  sorry

example : ∃ n, 0 < TriangularNumber n ∧ 3 ∣ TriangularNumber n := by
  sorry
























theorem infinitude_of_primes : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  -- prove using `Nat.exists_prime_and_dvd`
  sorry


















-- A product of a sum of squares is a sum of squares.
theorem brahmagupta_fibonacci (a b c d : ℤ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  sorry


























/-
Algebraic structures
-/

-- Let `G` be a group
variable {G : Type} [Group G]
variable (a b c : G)

-- We can use the usual multiplicative notation
example : a * (b * c) = (a * b) * c :=
  sorry

-- Let `R` be a commutative ring
variable {R : Type} [CommRing R]















/-
A few confusing things / subtle things
-/

variable (x : ℕ)

/- Coercions -/

-- #check x
-- #check -1
-- #check (-1 : ℤ) + x

-- example (a b : ℕ) (H : a ≤ b) : (a : ℤ) ≤ b := by
--   sorry

/- Junk values -/
-- #check 1 / 0
-- #eval 1 / 0
-- #check 1 / 2
-- #eval 1 / 2
-- #check √(- 8)
