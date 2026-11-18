module

public import Mathlib

public section

section Induction

lemma key_identity (n : ℕ) :
    (n + 1) ^ 3 + 2 * (n + 1) = n ^ 3 + 3 * n ^ 2 + 5 * n + 3 := by
  sorry

end Induction

section Sets

example (A B : Set ℕ) (x : ℕ) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  sorry

example (A B : Set ℕ) (x : ℕ) :
    x ∈ (A ∪ B) \ (A ∩ B) ↔ x ∈ A ∧ x ∉ B ∨ x ∉ A ∧ x ∈ B := by
  sorry

end Sets



section FiniteAndSums

/- This is the sum `∑ i ∈ {1, 2, 3} = 6`. -/
example : ∑ i ∈ Finset.Icc 1 3, i = 6 := by
  sorry

example (n : ℕ) : 2 * ∑ i ∈ Finset.Icc 1 n, i = n * (n + 1) := by
  sorry

end FiniteAndSums

/-- `√2` is irrational. -/
theorem irrational_root_two : Irrational √2 := by
  sorry


theorem irrational_root_prime (p : ℕ) (hp : Nat.Prime p) :
    Irrational √p := by
  sorry

end
