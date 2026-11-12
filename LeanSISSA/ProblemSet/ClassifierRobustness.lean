import Mathlib

/-! # Robustness of a linear classifier

This is an open exercise. Write the definitions and replace `True` as the docstrings specify.
Useful declarations: `Finset.abs_sum_le_sum_abs`, `Finset.sum_add_distrib`, `Real.sqrt_mul_self`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html
-/
noncomputable section

namespace LeanSISSA.ClassifierRobustness

/-- This function gives the score `∑ i, w i * x i + b` of a linear classifier.
The feature vector has a finite number of real entries. -/
def score {ι : Type*} [Fintype ι] (w x : ι → ℝ) (b : ℝ) : ℝ := by
  sorry

/-- This function gives the Euclidean norm `sqrt (∑ i, v i ^ 2)` of a finite real vector. -/
noncomputable def vectorNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := by
  sorry

/-- Assume that `score w x b` is positive and `vectorNorm w * vectorNorm δ < score w x b`.
Then the score at `fun i => x i + δ i` is positive.
Replace `True` with this statement. Use the Cauchy–Schwarz inequality to prove the statement. -/
theorem positive_under_perturbation {ι : Type*} [Fintype ι]
    (w x δ : ι → ℝ) (b : ℝ) : True := by
  sorry

end LeanSISSA.ClassifierRobustness
