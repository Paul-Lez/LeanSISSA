import Mathlib

/-! # Softmax

This exercise gives the definitions and statements.
Prove the properties of softmax on a nonempty finite type.
Useful declarations: `Real.exp_pos`, `Real.exp_add`, `Finset.sum_pos`, `Finset.sum_div`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Exp.html
-/
noncomputable section

namespace LeanSISSA.Softmax

/-- This function gives the softmax probability for index `i` in a finite set of scores. -/
noncomputable def softmax {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (x i) / ∑ j, Real.exp (x j)

/-- Each softmax probability is positive. -/
theorem softmax_pos {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    0 < softmax x i := by
  sorry

/-- The sum of the softmax probabilities is one. -/
theorem softmax_sum {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∑ i, softmax x i = 1 := by
  sorry

/-- Add the same constant to each score. The softmax probabilities do not change. -/
theorem softmax_add_const {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (c : ℝ) (i : ι) :
    softmax (fun j => x j + c) i = softmax x i := by
  sorry

end LeanSISSA.Softmax
