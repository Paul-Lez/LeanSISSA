module

public import Mathlib

/-! # Softmax

This exercise gives the definitions and statements.
Prove the properties of softmax on a nonempty finite type.
Useful declarations: `Real.exp_pos`, `Real.exp_add`, `Finset.sum_pos`, `Finset.sum_div`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Exp.html
-/

public section
noncomputable section

namespace LeanSISSA.Softmax

/-- This function gives the softmax probability for index `i` in a finite set of scores. -/
noncomputable def softmax {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (x i) / ∑ j, Real.exp (x j)

/-- The softmax normalizing constant is positive on a nonempty finite type. -/
lemma normalizer_pos {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    0 < ∑ j, Real.exp (x j) := by
  exact Finset.sum_pos (fun i _ => Real.exp_pos (x i)) Finset.univ_nonempty

/-- Each softmax probability is positive. -/
theorem softmax_pos {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (i : ι) :
    0 < softmax x i := by
  exact div_pos (Real.exp_pos _) (normalizer_pos x)

/-- The sum of the softmax probabilities is one. -/
theorem softmax_sum {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∑ i, softmax x i = 1 := by
  simp only [softmax, ← Finset.sum_div]
  exact div_self (ne_of_gt (normalizer_pos x))

/-- Add the same constant to each score. The softmax probabilities do not change. -/
theorem softmax_add_const {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (c : ℝ) (i : ι) :
    softmax (fun j => x j + c) i = softmax x i := by
  simp only [softmax, Real.exp_add, ← Finset.sum_mul]
  exact mul_div_mul_right _ _ (ne_of_gt (Real.exp_pos c))

end LeanSISSA.Softmax
