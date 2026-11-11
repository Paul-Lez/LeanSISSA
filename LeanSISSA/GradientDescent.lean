import Mathlib

/-! # Gradient descent on a quadratic

This exercise gives the definitions and statements.
Useful declarations: `sq_nonneg`, `mul_nonneg`, `abs_mul`, `pow_two`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Deriv/Basic.html
-/
noncomputable section

namespace LeanSISSA.GradientDescent

/-- This function gives the squared distance from `x` to the minimizer `a`. -/
def loss (a x : ℝ) : ℝ := (x - a) ^ 2

/-- This function gives one gradient descent step for `loss a`.
The derivative of `loss a` at `x` is `2 * (x - a)`. -/
def step (a η x : ℝ) : ℝ := x - η * (2 * (x - a))

/-- If the learning rate is between zero and one, the step does not increase the quadratic loss.
The bounds include zero and one. -/
theorem loss_step_le (a η x : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1) :
    loss a (step a η x) ≤ loss a x := by
  sorry

/-- If the learning rate is strictly between zero and one, the step decreases the loss at `x ≠ a`. -/
theorem loss_step_lt (a η x : ℝ) (hη₀ : 0 < η) (hη₁ : η < 1) (hx : x ≠ a) :
    loss a (step a η x) < loss a x := by
  sorry

end LeanSISSA.GradientDescent
