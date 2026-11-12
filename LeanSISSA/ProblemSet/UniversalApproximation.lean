import Mathlib

/-! # Universal approximation with ReLU

This exercise gives the definitions and statement. It is a difficult exercise.
First, examine simple piecewise-linear functions.
Useful declarations: `ContinuousOn`, `Set.Icc`, `Finset.sum`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousOn.html
-/
noncomputable section

namespace LeanSISSA.UniversalApproximation

/-- This function gives a real-valued ReLU network with one hidden layer and `n` hidden neurons.
The input and output are real numbers. The output bias is `c`. -/
def network (n : ℕ) (a w b : Fin n → ℝ) (c x : ℝ) : ℝ :=
  c + ∑ i, a i * max 0 (w i * x + b i)

/-- Let `f` be continuous on `[0, 1]` and let `ε` be positive.
There is a ReLU network with one hidden layer whose error is less than `ε` at every point in `[0, 1]`. -/
theorem approximate (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (a w b : Fin n → ℝ) (c : ℝ),
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |network n a w b c x - f x| < ε := by
  sorry

end LeanSISSA.UniversalApproximation
