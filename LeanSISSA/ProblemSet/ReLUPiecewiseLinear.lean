import Mathlib

/-! # ReLU networks are piecewise linear

This is an open exercise. Write the definitions and replace `True` with the stated property.
Useful declarations: `Finset.sum`, `Set.Finite`, `max_eq_left`, `max_eq_right`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Finite/Basic.html
-/
noncomputable section

namespace LeanSISSA.ReLUPiecewiseLinear

/-- This function gives a ReLU network with one input, one output, and one hidden layer.
The output is `c + ∑ i, a i * max 0 (w i * x + b i)`. -/
def network (n : ℕ) (a w b : Fin n → ℝ) (c x : ℝ) : ℝ := by
  sorry

/-- This condition says that `f` is locally affine outside a finite set `S`.
For each `x ∉ S`, there is an open interval around `x` on which `f` is affine. -/
def piecewiseAffine (f : ℝ → ℝ) : Prop :=
  sorry

/-- The network is locally affine outside a finite set.
Replace `True` with `piecewiseAffine (network n a w b c)`. Prove the statement. -/
theorem network_piecewiseAffine (n : ℕ) (a w b : Fin n → ℝ) (c : ℝ) : True := by
  sorry

end LeanSISSA.ReLUPiecewiseLinear
