module

public import LeanSISSA.GettingStarted.MoreExercises

public section


/-! # First steps in Lean

The goal of this file is to give you a few examples of how to write the Lean code corresponding to
various simple mathematical steps (e.g. "apply this equality" or "use standard algebraic
manipulations to simplify this expression").

In each case, the goal is to fill in the `sorry` with a Lean tactic proof, following
the hints in the comments.
-/

section UniversalQuantifiers

example : ∀ n, n ^ 2 + 2 * n + 1 = (n + 1) ^ 2 := by
  -- hint: use `intro` to introduce the variable `n`, and then use algebraic automation.
  intro n
  ring

end UniversalQuantifiers

section Existentials

theorem exists_example : ∃ x : ℕ, x ^ 2 = 4 := by
  -- hint: use `use` to provide a witness for the existential quantifier.
  use 2
  norm_num

theorem dvd_square (a b : ℕ) (H : a ∣ b) : a ∣ b ^ 2 := by
  -- use the `obtain` tactic to get a witness for the existential quantifier in `H`.
  -- Then use `use` to provide a witness for the existential quantifier in the goal.
  obtain ⟨c, rfl⟩ := H
  refine ⟨a * c ^ 2, ?_⟩
  ring

theorem square_dvd_square (a b : ℕ) (H : a ∣ b) : a ^ 2 ∣ b ^ 2 := by
  -- use the `obtain` tactic to get a witness for the existential quantifier in `H`.
  -- Then use `use` to provide a witness for the existential quantifier in the goal.
  obtain ⟨c, rfl⟩ := H
  refine ⟨c ^ 2, ?_⟩
  ring

end Existentials

section Induction

lemma three_div_sq_add_two_mul (n : ℕ) : 3 ∣ n ^ 3 + 2 * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [key_identity]
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + n ^ 2 + n + 1, ?_⟩
    nlinarith [hk]

end Induction

section FiniteAndSums

example (n : ℕ) : ∑ _i ∈ Finset.Icc 1 n, 1 = n := by
  rw [Finset.sum_const, Nat.card_Icc]
  simp

end FiniteAndSums

section Coercions

example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) : 0 < (a / b : ℚ) ∧ (a / b : ℚ) ≤ 1 := by
  /- Hints:
  - first use `constructor` to split this into two goals
  - For the first subgoal, use `Nat.cast_pos` and `div_pos`
  - For the second subgoal, use `Nat.cast_le` and `div_le_one_of_le₀`.
  -/
  constructor
  · exact div_pos (Nat.cast_pos.mpr ha) (Nat.cast_pos.mpr hb)
  · apply div_le_one_of_le₀
    · exact_mod_cast hab
    · exact_mod_cast Nat.zero_le b

example (a : ℕ) (ha : a ≠ 0) :  Real.exp 1 ≤ Real.exp a := by
  -- hint: first show that `1 ≤ a` using `Nat.one_le_iff_ne_zero` and `ha`,
  -- then use `Real.exp_le_exp`.
  apply Real.exp_le_exp.mpr
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha

end Coercions

section Inequalities

example (a b : ℝ) (h : a < b) : a + 1 < b + 1 := by
  -- hint: use `add_lt_add_right`.
  simpa [add_comm] using add_lt_add_right h 1

example (a b : ℝ) (ha : 0 ≤ a) (h : a < b) : a ^ 2 < b ^ 2 := by
  -- Since `0 ≤ a < b`, apply `sq_lt_sq₀`.
  exact (sq_lt_sq₀ ha (le_of_lt (ha.trans_lt h))).2 h

example (a b : ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by
  -- Use the nonnegativity of `(a - b) ^ 2` and clear the positive denominator.
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  nlinarith [sq_nonneg (a - b)]

example (a b c d e f g : ℝ) (ha : a ≤ b) (hb : b < c) (hc : c ≤ d)
    (hd : d ≤ e) (he : e ≤ f) (hf : f ≤ g) : a < g := by
  /-
  hint: if you enjoy pain, use `lt_of_le_of_lt` and `lt_of_lt_of_le` repeatedly.
  Otherwise, use `linarith`.
  -/
  linarith

end Inequalities


theorem primes_dvd (a b p : ℕ) (hp : Prime p) (h : p ∣ a ^ 2 * b) :
    p ∣ a ∨ p ∣ b := by
  rcases hp.dvd_mul.mp h with ha | hb
  · exact Or.inl (hp.dvd_of_dvd_pow ha)
  · exact Or.inr hb



section Continuity

open Real

/-- The sigmoid function. -/
noncomputable def σ : ℝ → ℝ := fun x => (1 + exp (-x))⁻¹

lemma σ_pos : ∀ x, 0 < 1 + exp x := by
  intro x
  exact add_pos zero_lt_one (exp_pos x)

theorem sigmoid_continous : Continuous σ := by
  apply Continuous.inv₀ (continuous_const.add (Real.continuous_exp.comp continuous_neg))
  intro x
  exact ne_of_gt (σ_pos (-x))

theorem sigmoid_differentiable : Differentiable ℝ σ := by
  change Differentiable ℝ (fun x : ℝ => (1 + exp (-x))⁻¹)
  have hDen : Differentiable ℝ (fun x : ℝ => 1 + exp (-x)) := by fun_prop
  exact hDen.inv (fun x => ne_of_gt (σ_pos (-x)))

theorem sigmoid_derivative (x : ℝ) : deriv σ x = σ x * (1 - σ x) := by
  have hExp : HasDerivAt (fun y : ℝ => exp (-y)) (-exp (-x)) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hDen : HasDerivAt (fun y : ℝ => 1 + exp (-y)) (-exp (-x)) x :=
    hExp.const_add 1
  have hInv := hDen.inv (ne_of_gt (σ_pos (-x)))
  change deriv ((fun y : ℝ => 1 + exp (-y))⁻¹) x = _
  rw [hInv.deriv]
  dsimp [σ]
  field_simp [ne_of_gt (σ_pos (-x))]
  ring

end Continuity
