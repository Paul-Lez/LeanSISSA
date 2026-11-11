import Mathlib

/-! # The exponential function and an ODE

This exercise gives the statements for the equation `f' = f`.
Prove each statement. The ODE uniqueness theorem is one possible tool.
Useful declarations: `ODE_solution_unique_univ`, `LipschitzWith.id`, `Real.hasDerivAt_exp`,
`HasDerivAt.const_smul`, `deriv_const_smul`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/ExistUnique.html
-/

open Metric Set Asymptotics Filter Real
open scoped Topology NNReal

namespace LeanSISSA.ExponentialODE

/-- Let `f` satisfy `f' = f` at every real number. If `f` is zero at one point, it is zero
at every point. -/
theorem eq_zero_of_hasDeriv_self_of_eval_zero
    {f : ℝ → ℝ} (hx : ∀ x, HasDerivAt f (f x) x)
    {t₀ : ℝ} (ht₀ : f t₀ = 0) : f = 0 := by
  sorry

/-- Each solution of `f' = f` on the real numbers is a constant multiple of `Real.exp`. -/
theorem exists_smul_rexp {f : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f x) x) :
    ∃ (C : ℝ), f = C • Real.exp := by
  sorry

/-- The equation `f' = f` holds at every real number if and only if `f` is a constant
multiple of `Real.exp`. -/
theorem forall_hasDerivAt_eval_self_iff (f : ℝ → ℝ) :
    (∀ x, HasDerivAt f (f x) x) ↔ ∃ (C : ℝ), f = C • Real.exp := by
  sorry

/-- For a differentiable real function `f`, the equation `deriv f = f` holds if and only if
`f` is a constant multiple of `Real.exp`. -/
theorem deriv_eq_self_iff {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv f = f ↔ ∃ (C : ℝ), f = C • Real.exp := by
  sorry

end LeanSISSA.ExponentialODE
