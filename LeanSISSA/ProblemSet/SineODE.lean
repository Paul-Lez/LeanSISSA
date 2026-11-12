import Mathlib

/-! # The sine function and an ODE

This exercise uses the first-order system `f' = g` and `g' = -f`.
The system expresses the equation `f'' = -f` without an iterated derivative.
Use the product-valued function `fun x => (f x, g x)`.
Its vector field is `fun y : ℝ × ℝ => (y.2, -y.1)`.
Prove that the vector field is Lipschitz. Then use uniqueness for the product-valued ODE.
Useful declarations: `HasDerivAt.prodMk`, `LipschitzWith.prod_fst`,
`LipschitzWith.prod_snd`, `LipschitzWith.neg`, `LipschitzWith.prodMk`,
`ODE_solution_unique_univ`, `Real.hasDerivAt_sin`, `Real.hasDerivAt_cos`,
`Real.sin_zero`, `Real.cos_zero`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/ExistUnique.html
-/

namespace LeanSISSA.SineODE

/-- A solution of `f' = g` and `g' = -f` is a linear combination of sine and cosine.
The initial values are the coefficients of cosine and sine, respectively. -/
theorem solution_eq (f g : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (-f x) x) :
    ∀ x, f x = f 0 * Real.cos x + g 0 * Real.sin x := by
  sorry

/-- If `f' = g`, `g' = -f`, `f 0 = 0`, and `g 0 = 1`, then `f` is the sine function. -/
theorem eq_sin (f g : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (-f x) x)
    (hf0 : f 0 = 0) (hg0 : g 0 = 1) : f = Real.sin := by
  sorry

end LeanSISSA.SineODE
