import Mathlib

/-! # Least squares and orthogonality

This is an open exercise. Replace each placeholder as the docstring specifies.
Useful declarations: `Finset.sum_add_distrib`, `Finset.sum_mul`, `sq_nonneg`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html
-/
noncomputable section

namespace LeanSISSA.LeastSquares

/-- This function gives the sum of squared residuals for a finite data matrix.
The sum is `∑ i, ((∑ j, X i j * w j) - y i)^2`. -/
def loss {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → κ → ℝ) (y : ι → ℝ) (w : κ → ℝ) : ℝ := by
  sorry

/-- Assume that `w` minimizes `loss X y` over all coefficient vectors.
Then the residual is orthogonal to every column of `X`.
For every `j`, the sum `∑ i, X i j * ((∑ k, X i k * w k) - y i)` is zero.
Replace `True` with this statement. Prove the statement. -/
theorem residual_orthogonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → κ → ℝ) (y : ι → ℝ) (w : κ → ℝ) : True := by
  sorry

end LeanSISSA.LeastSquares
