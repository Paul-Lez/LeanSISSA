module

public import Mathlib

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

public section

namespace LeanSISSA.SineODE

private theorem vectorField_lipschitz :
    LipschitzWith (1 : NNReal) (fun y : ℝ × ℝ => (y.2, -y.1)) := by
  have h₁ : LipschitzWith (1 : NNReal) (fun y : ℝ × ℝ => y.2) := LipschitzWith.prod_snd
  have h₂ : LipschitzWith (1 : NNReal) (fun y : ℝ × ℝ => -y.1) :=
    LipschitzWith.neg LipschitzWith.prod_fst
  simpa using h₁.prodMk h₂

/-- Solutions of the system are determined by their initial values. -/
theorem solution_eq (f g : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (-f x) x) :
    ∀ x, f x = f 0 * Real.cos x + g 0 * Real.sin x := by
  let u : ℝ → ℝ := fun x => f 0 * Real.cos x + g 0 * Real.sin x
  let v : ℝ → ℝ := fun x => -f 0 * Real.sin x + g 0 * Real.cos x
  have hu (x : ℝ) : HasDerivAt u (v x) x := by
    dsimp [u, v]
    convert ((Real.hasDerivAt_cos x).const_mul (f 0)).add
      ((Real.hasDerivAt_sin x).const_mul (g 0)) using 1 <;> ring
  have hv (x : ℝ) : HasDerivAt v (-u x) x := by
    dsimp [u, v]
    convert ((Real.hasDerivAt_sin x).const_mul (-f 0)).add
      ((Real.hasDerivAt_cos x).const_mul (g 0)) using 1 <;> ring
  have h := ODE_solution_unique_univ
    (v := fun (_ : ℝ) (y : ℝ × ℝ) => (y.2, -y.1))
    (s := fun _ => Set.univ) (K := 1) (t₀ := 0)
    (f := fun x => (f x, g x)) (g := fun x => (u x, v x))
    (fun _ => vectorField_lipschitz.lipschitzOnWith)
    (fun x => ⟨(hf x).prodMk (hg x), Set.mem_univ _⟩)
    (fun x => ⟨(hu x).prodMk (hv x), Set.mem_univ _⟩) (by simp [u, v])
  intro x
  have := congrFun h x
  exact congrArg Prod.fst this

/-- The initial values `0` and `1` give the sine solution. -/
theorem eq_sin (f g : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (-f x) x)
    (hf0 : f 0 = 0) (hg0 : g 0 = 1) : f = Real.sin := by
  funext x
  rw [solution_eq f g hf hg x, hf0, hg0]
  simp

/-- A solution of `f' = g`, `g' = -f` with `f 0 = 1` and `g 0 = 0` is cosine.
Hint: `funext`, `solution_eq`, and `simp`. -/
theorem cosine_initial_values (f g : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (-f x) x)
    (hf0 : f 0 = 1) (hg0 : g 0 = 0) : f = Real.cos := by
  funext x
  simpa [hf0, hg0] using solution_eq f g hf hg x


end LeanSISSA.SineODE
