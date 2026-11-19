module

public import Mathlib

/-! # Ordinary least squares

Solve linear regression through the origin.
Useful declarations: `Finset.sum_add_distrib`, `Finset.sum_mul`, `Finset.mul_sum`, `sq_nonneg`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Ring/Finset.html
-/

public section

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

private lemma loss_expand (n : ℕ) (x y : Fin n → ℝ) (β : ℝ) :
    loss n x y β = β ^ 2 * (∑ i, (x i) ^ 2) -
      2 * β * (∑ i, x i * y i) + ∑ i, (y i) ^ 2 := by
  unfold loss
  calc
    (∑ i, (β * x i - y i) ^ 2) =
        ∑ i, (β ^ 2 * (x i) ^ 2 - 2 * β * (x i * y i) + (y i) ^ 2) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = β ^ 2 * (∑ i, (x i) ^ 2) -
        2 * β * (∑ i, x i * y i) + ∑ i, (y i) ^ 2 := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum]

/-- Assume that the sum of squared inputs is positive.
The coefficient from the formula minimizes the loss over all real coefficients. -/
theorem coefficient_minimises (n : ℕ) (x y : Fin n → ℝ)
    (hx : 0 < ∑ i, (x i) ^ 2) (β : ℝ) :
    loss n x y (coefficient n x y) ≤ loss n x y β := by
  let d := ∑ i, (x i) ^ 2
  let c := ∑ i, x i * y i
  have hd : d ≠ 0 := ne_of_gt hx
  have hc : coefficient n x y * d = c := by
    dsimp [coefficient, d, c]
    field_simp
  rw [loss_expand, loss_expand]
  dsimp [d, c] at *
  rw [← hc]
  nlinarith [sq_nonneg (β - coefficient n x y)]

/-- Assume that the sum of squared inputs is positive.
Each minimizer is equal to the coefficient from the formula. -/
theorem minimiser_unique (n : ℕ) (x y : Fin n → ℝ)
    (hx : 0 < ∑ i, (x i) ^ 2) (β : ℝ)
    (hβ : ∀ t, loss n x y β ≤ loss n x y t) : β = coefficient n x y := by
  let d := ∑ i, (x i) ^ 2
  have hd : 0 < d := by simpa [d] using hx
  have hmin := hβ (coefficient n x y)
  rw [loss_expand, loss_expand] at hmin
  have hc : coefficient n x y * d = ∑ i, x i * y i := by
    dsimp [coefficient, d]
    field_simp
  dsimp [d] at hc
  rw [← hc] at hmin
  have hsquare : (β - coefficient n x y) ^ 2 = 0 := by nlinarith [sq_nonneg (β - coefficient n x y)]
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)

end LeanSISSA.OrdinaryLeastSquares
