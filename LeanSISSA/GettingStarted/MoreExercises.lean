module

public import Mathlib

public section

section Induction

lemma key_identity (n : ℕ) :
    (n + 1) ^ 3 + 2 * (n + 1) = n ^ 3 + 3 * n ^ 2 + 5 * n + 3 := by
  ring

end Induction

section Sets

example (A B : Set ℕ) (x : ℕ) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B := by
  simp

example (A B : Set ℕ) (x : ℕ) :
    x ∈ (A ∪ B) \ (A ∩ B) ↔ x ∈ A ∧ x ∉ B ∨ x ∉ A ∧ x ∈ B := by
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]
  tauto

end Sets



section FiniteAndSums

/- This is the sum `∑ i ∈ {1, 2, 3} = 6`. -/
example : ∑ i ∈ Finset.Icc 1 3, i = 6 := by
  norm_num [Finset.sum_Icc_succ_top]

example (n : ℕ) : 2 * ∑ i ∈ Finset.Icc 1 n, i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      nlinarith [ih]

end FiniteAndSums

/-- `√2` is irrational. -/
theorem irrational_root_two : Irrational √2 := by
  simpa using Nat.prime_two.irrational_sqrt


theorem irrational_root_prime (p : ℕ) (hp : Nat.Prime p) :
    Irrational √p := by
  exact hp.irrational_sqrt

end
