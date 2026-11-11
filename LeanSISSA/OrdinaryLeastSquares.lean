import Mathlib

/-! # Ordinary least squares

This exercise gives the definitions and statements. Solve linear regression through the origin.
For a harder exercise, add an intercept or use a design matrix.
Useful declarations: `Finset.sum_add_distrib`, `Finset.sum_mul`, `Finset.mul_sum`, `sq_nonneg`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Ring/Finset.html
-/

noncomputable section
namespace LeanSISSA.OrdinaryLeastSquares

/-- This function gives the sum of squared residuals for `n` observations.
The prediction for observation `i` is `β * x i`. -/
def loss (n : ℕ) (x y : Fin n → ℝ) (β : ℝ) : ℝ :=
  ∑ i, (β * x i - y i) ^ 2

/-- This function gives the coefficient `(∑ i, x i * y i) / (∑ i, (x i)^2)`.
The formula is for least squares with a line through the origin.
The denominator is nonzero if at least one input is nonzero. -/
def coefficient (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  (∑ i, x i * y i) / ∑ i, (x i) ^ 2

/-- Assume that the sum of squared inputs is positive.
The coefficient from the formula minimizes the loss over all real coefficients. -/
theorem coefficient_minimises (n : ℕ) (x y : Fin n → ℝ)
    (hx : 0 < ∑ i, (x i) ^ 2) (β : ℝ) :
    loss n x y (coefficient n x y) ≤ loss n x y β := by
  sorry

/-- Assume that the sum of squared inputs is positive.
Each minimizer is equal to the coefficient from the formula. -/
theorem minimiser_unique (n : ℕ) (x y : Fin n → ℝ)
    (hx : 0 < ∑ i, (x i) ^ 2) (β : ℝ)
    (hβ : ∀ t, loss n x y β ≤ loss n x y t) : β = coefficient n x y := by
  sorry

end LeanSISSA.OrdinaryLeastSquares
