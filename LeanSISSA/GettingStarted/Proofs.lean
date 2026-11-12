import Mathlib


/-! # First steps in Lean

The goal of this file is to give you a few examples of how to write the Lean code corresponding to
various simple mathematical steps (e.g. "apply this equality" or "use standard algebraic
manipulations to simplify this expression").

In each case, the goal is to fill in the `sorry` with a Lean tactic proof, following
the hints in the comments.
-/

section UniversalQuantifiers
-- TODO: this is so people can try the `intro` tactic.

end UniversalQuantifiers

section Existentials

theorem exists_example : ∃ x : ℕ, x ^ 2 = 4 := by
  -- hint: use `use` to provide a witness for the existential quantifier.
  sorry

theorem dvd_square (a b : ℕ) (H : a ∣ b) : a ∣ b ^ 2 := by
  -- use the `obtain` tactic to get a witness for the existential quantifier in `H`.
  -- Then use `use` to provide a witness for the existential quantifier in the goal.
  sorry

theorem square_dvd_square (a b : ℕ) (H : a ∣ b) : a ^ 2 ∣ b ^ 2 := by
  -- use the `obtain` tactic to get a witness for the existential quantifier in `H`.
  -- Then use `use` to provide a witness for the existential quantifier in the goal.
  sorry

end Existentials

section Finite

-- Introduce finite types, finite sets, notation for sums over these


end Finite


section Coercions

example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) : 0 < (a / b : ℚ) ∧ (a / b : ℚ) ≤ 1 := by
  /- Hints:
  - first use `constructor` to split this into two goals
  - For the first subgoal: use `Nat.cast_pos`, `Nat.cast_le` and `div_pos`
  - For the second subgoal: use `Nat.cast_le` and `div_le_one_of_le`.
  -/
  sorry

example (a : ℕ) (ha : a ≠ 0) :  Real.exp 1 ≤ Real.exp a := by
  -- hint: first show that `1 ≤ a` using `Nat.one_le_iff_ne_zero` and `ha`,
  -- then use `Real.exp_le_exp`.
  sorry

end Coercions

section Inequalities

example (a b : ℝ) (h : a < b) : a + 1 < b + 1 := by
  -- hint: use `add_lt_add_right`.
  sorry

example (a b : ℝ) (h : a < b) : a ^ 2 < b ^ 2 := by
  -- hint: use `Real.sq_lt_sq`
  sorry

example (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  -- hint: use `Real.mul_self_nonneg` and `Real.le_div_iff`
  sorry

example (a b c d e f g : ℝ) (ha : a ≤ b) (hb : b < c) (hc : c ≤ d)
    (hd : d ≤ e) (he : e ≤ f) (hf : f ≤ g) :
    a < g := by
  /-
  hint: if you enjoy pain, use `lt_of_le_of_lt` and `lt_of_lt_of_le` repeatedly.
  otherwise try using `linarith` or (for the cool kids) `grw`
  (a bit like `rw` but for inequalities).
  -/
  sorry

end Inequalities



section Continuity

open Real

/-- The sigmoid function. -/
noncomputable def σ : ℝ → ℝ := fun x => (1 + exp x)⁻¹

lemma sigmoid_pos : ∀ x, 0 < 1 + exp x := by
  intro x
  apply add_pos
  · exact zero_lt_one
  · apply exp_pos

theorem sigmoid_continous : Continuous σ := by
  unfold σ
  apply Continuous.inv₀
  · continuity
  · intro x
    apply ne_of_gt
    apply _root_.sigmoid_pos

theorem sigmoid_differentiable : Differentiable ℝ σ := by
  sorry

theorem sigmoid_derivative (x : ℝ) : deriv σ x = σ x * (1 - σ x) := by
  sorry

end Continuity

section Induction

lemma key_identity (n : ℕ) : (n + 1) ^ 2 + 2 * (n + 1) = n ^ 2 + 4 * n + 3 := by
  sorry

lemma three_div_sq_add_two_mul (n : ℕ) : 3 ∣ n ^ 2 + 2 * n := by
  sorry

end Induction




theorem primes_dvd (a b p : ℕ) (hp : Prime p) (h : p ∣ a ^ 2 * b) :
    p ∣ a ∨ p ∣ b := by
  sorry


/-- `√2` is irrational. -/
theorem irrational_root_two : Irrational √2 := by
  sorry

open scoped Real

/-- `π` is irrational. -/
theorem irrational_π : Irrational π := by
  sorry

/-- Every positive integer can be written as a sum of distinct Fibonacci numbers. -/
theorem zeckendorf (n : ℕ) (hn : 0 < n) :
    ∃ s : Finset ℕ, s.sum Nat.fib = n := by
  sorry
