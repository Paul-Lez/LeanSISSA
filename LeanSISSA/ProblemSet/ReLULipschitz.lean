module

public import Mathlib

/-! # ReLU and Lipschitz continuity

This exercise gives the definitions and statements.
Useful declarations: `max_le_max`, `abs_le`, `LipschitzWith.comp`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Lipschitz.html
-/

public section
noncomputable section

namespace LeanSISSA.ReLULipschitz

/-- This function gives the rectified linear unit. The result is zero if `x` is negative.
Otherwise, the result is `x`. -/
def relu (x : ℝ) : ℝ := max 0 x

/-- ReLU sends zero to zero. Hint: unfold `relu` and use `simp`. -/
theorem relu_zero : relu 0 = 0 := by
  sorry

/-- ReLU sends nonpositive inputs to zero. Hint: `max_eq_left`. -/
theorem relu_of_nonpos (x : ℝ) (hx : x ≤ 0) : relu x = 0 := by
  sorry

/-- ReLU is nonnegative. Hint: `le_max_left`. -/
theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := by
  sorry

/-- Applying ReLU twice gives the same result. Hint: use nonnegativity. -/
theorem relu_idempotent (x : ℝ) : relu (relu x) = relu x := by
  sorry

/-- The absolute difference between two ReLU outputs is at most the
absolute difference between their inputs. -/
theorem relu_lipschitz (x y : ℝ) : |relu x - relu y| ≤ |x - y| := by
  sorry

/-- The composition has the Lipschitz bound `K * L`.
The hypotheses give Lipschitz bounds `K` and `L` for `f` and `g`, with `K ≥ 0`. -/
theorem lipschitz_comp (f g : ℝ → ℝ) (K L : ℝ)
    (hf : ∀ x y, |f x - f y| ≤ K * |x - y|)
    (hg : ∀ x y, |g x - g y| ≤ L * |x - y|) (hK : 0 ≤ K) :
    ∀ x y, |f (g x) - f (g y)| ≤ (K * L) * |x - y| := by
  sorry

end LeanSISSA.ReLULipschitz
