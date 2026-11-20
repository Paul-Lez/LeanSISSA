module

public import LeanSISSA.GettingStarted.MoreExercises

public section


/-! # First steps in Lean

The goal of this file is to give you a few examples of how to write the Lean code corresponding to
various simple mathematical steps (e.g. "apply this equality" or "use standard algebraic
manipulations to simplify this expression").

In each case, the goal is to fill in the `sorry` with a Lean tactic proof, following
the hints in the comments.

Note: if you find yourself looking for a lemma, you can use loogle (which you can access in VS Code by
opening the Lean menu and selecting "Search with Loogle").
-/

section UniversalQuantifiers

example : ∀ n, n ^ 2 + 2 * n + 1 = (n + 1) ^ 2 := by
  -- hint: use `intro` to introduce the variable `n`, and then use algebraic automation
  -- such as the `ring` tactic, or `rw` with the appropriate lemmas: `add_pow_two`, `mul_one`, `one_pow`.
  sorry

end UniversalQuantifiers

section Existentials

theorem exists_example : ∃ x : ℕ, x ^ 2 = 4 := by
  -- hint: use `use` to provide a witness for the existential quantifier.
  sorry

theorem dvd_square (a b : ℕ) (H : a ∣ b) : a ∣ b ^ 2 := by
  -- use the `obtain` tactic to get a witness for the existential quantifier in `H`.
  -- Here, given a hypothesis `H : a ∣ b`, writing `obtain ⟨c, hc⟩ := H`
  -- will produce a `c` such that `b = a * c`.
  -- Then use `use` to provide a witness for the existential quantifier in the goal.
  -- To do algebraic manipulations, you can use `grind` or `rw` with the
  -- appropriate lemmas: `pow_two`, `mul_assoc`, `mul_comm`.
  sorry

theorem square_dvd_square (a b : ℕ) (H : a ∣ b) : a ^ 2 ∣ b ^ 2 := by
  -- use the `obtain` tactic to get a witness for the existential quantifier in `H`.
  -- Here, given a hypothesis `H : a ∣ b`, writing `obtain ⟨c, hc⟩ := H`
  -- will produce a `c` such that `b = a * c`.
  -- Then use `use` to provide a witness for the existential quantifier in the goal.
  sorry

end Existentials

section Induction

#check key_identity

lemma three_div_sq_add_two_mul (n : ℕ) : 3 ∣ n ^ 3 + 2 * n := by
  induction n with
  | zero => sorry
  | succ n ih =>
    -- hint: use `rw` to rewrite the goal using the lemma `key_identity`
    -- (see the goal printed in `#check key_identity` above),
    -- and then use `obtain` to get a witness for the existential quantifier in `ih`.
    -- hint: use `use` to provide a witness for the existential quantifier in the goal.
    -- (the goal is `3 ∣ (some expression)`, which in Lean means `∃ k, (some expression) = 3 * k`,
    -- so you can use `use` to provide a witness for `k`).
    sorry


end Induction

section FiniteAndSums

example (n : ℕ) : ∑ i ∈ Finset.Icc 1 n, 1 = n := by
  -- hint: use `Finset.sum_const_nat` and `Nat.card_Icc`.
  sorry

end FiniteAndSums

section Coercions

example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) : 0 < (a / b : ℚ) ∧ (a / b : ℚ) ≤ 1 := by
  /- Hints:
  - first use `constructor` to split this into two goals
  - For the first subgoal: use `Nat.cast_pos`, `Nat.cast_le` and `div_pos`
  - For the second subgoal: use `Nat.cast_le` and `div_le_one_of_le`.

  Here note the strange arrows in the goal, e.g `↑a` and so on. In Lean these are "coercions".
  What's happening is that the goal is an inequality of rational numbers, and so Lean is
  automatically converting the natural numbers `a` and `b` into rational numbers
  (i.e. applyig the canonical inclusion from `ℕ` to `ℚ`). The coercion is denoted by the arrow `↑`.
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

example (a b : ℝ) (ha : 0 ≤ a) (h : a < b) : a ^ 2 < b ^ 2 := by
  -- hint: use `Real.sq_lt_sq`
  sorry

example (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  -- hint: use `Real.mul_self_nonneg` and `Real.le_div_iff`
  sorry

example (a b c d e f g : ℝ) (ha : a ≤ b) (hb : b < c) (hc : c ≤ d)
    (hd : d ≤ e) (he : e ≤ f) (hf : f ≤ g) : a < g := by
  /-
  hint: if you enjoy pain, use `lt_of_le_of_lt` and `lt_of_lt_of_le` repeatedly.
  Otherwise, use `linarith`.
  -/
  sorry

end Inequalities


theorem primes_dvd (a b p : ℕ) (hp : Prime p) (h : p ∣ a ^ 2 * b) :
    p ∣ a ∨ p ∣ b := by
  sorry



section Continuity

open Real

/-- The sigmoid function. -/
noncomputable def σ : ℝ → ℝ := fun x => (1 + exp (-x))⁻¹

lemma σ_pos : ∀ x, 0 < 1 + exp x := by
  -- use add_pos, zero_lt_one, exp_pos
  sorry

theorem sigmoid_continous : Continuous σ := by
  -- Continuous.inv₀, ne_of_gt, σ_pos and the continuity tactic.
  sorry

theorem sigmoid_differentiable : Differentiable ℝ σ := by
  sorry

theorem sigmoid_derivative (x : ℝ) : deriv σ x = σ x * (1 - σ x) := by
  sorry

end Continuity
