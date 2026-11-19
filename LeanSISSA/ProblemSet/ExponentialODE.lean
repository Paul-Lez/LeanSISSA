module

public import Mathlib

/-! # The exponential function and an ODE

This exercise gives the statements for the equation `f' = f`.
Prove each statement. The ODE uniqueness theorem is one possible tool.
Useful declarations: `ODE_solution_unique_univ`, `LipschitzWith.id`, `Real.hasDerivAt_exp`,
`HasDerivAt.const_smul`, `deriv_const_smul`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/ODE/ExistUnique.html
-/

public section

open Metric Set Asymptotics Filter Real
open scoped Topology NNReal

namespace LeanSISSA.ExponentialODE

/-- If `f' = f` everywhere and `f` vanishes at one point, it vanishes everywhere. -/
theorem eq_zero_of_hasDeriv_self_of_eval_zero
    {f : ℝ → ℝ} (hx : ∀ x, HasDerivAt f (f x) x)
    {t₀ : ℝ} (ht₀ : f t₀ = 0) : f = 0 := by
  apply ODE_solution_unique_univ (v := fun _ y : ℝ => y)
    (s := fun _ => Set.univ) (K := 1) (t₀ := t₀)
  · intro t; exact (LipschitzWith.id : LipschitzWith 1 (fun y : ℝ => y)).lipschitzOnWith
  · intro t; exact ⟨hx t, mem_univ _⟩
  · intro t; exact ⟨hasDerivAt_const t (0 : ℝ), mem_univ _⟩
  · simp [ht₀]

/-- Every solution of `f' = f` is a constant multiple of `Real.exp`. -/
theorem exists_smul_rexp {f : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f x) x) :
    ∃ (C : ℝ), f = C • Real.exp := by
  refine ⟨f 0, ?_⟩
  apply ODE_solution_unique_univ (v := fun _ y : ℝ => y)
    (s := fun _ => Set.univ) (K := 1) (t₀ := 0)
  · intro t; exact (LipschitzWith.id : LipschitzWith 1 (fun y : ℝ => y)).lipschitzOnWith
  · intro t; exact ⟨hf t, mem_univ _⟩
  · intro t
    have h := (Real.hasDerivAt_exp t).const_smul (f 0)
    simpa [smul_eq_mul, mul_comm] using h
  · simp [Real.exp_zero]

/-- The derivative equation holds exactly for constant multiples of `Real.exp`. -/
theorem forall_hasDerivAt_eval_self_iff (f : ℝ → ℝ) :
    (∀ x, HasDerivAt f (f x) x) ↔ ∃ (C : ℝ), f = C • Real.exp := by
  constructor
  · exact exists_smul_rexp
  · rintro ⟨C, rfl⟩ x
    simpa [smul_eq_mul, mul_comm] using (Real.hasDerivAt_exp x).const_smul C

/-- For differentiable `f`, `deriv f = f` exactly when `f` is a multiple of `Real.exp`. -/
theorem deriv_eq_self_iff {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv f = f ↔ ∃ (C : ℝ), f = C • Real.exp := by
  constructor
  · intro h
    apply (forall_hasDerivAt_eval_self_iff f).mp
    intro x
    exact (hf x).hasDerivAt.congr_deriv (by rw [h])
  · rintro ⟨C, rfl⟩
    funext x
    exact (Real.hasDerivAt_exp x).const_smul C |>.deriv

/-- A solution of `f' = f` with `f 0 = 1` is the exponential function.
Hint: use `exists_smul_rexp` and evaluate at zero with `congrFun`. -/
theorem exponential_initial_one (f : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f x) x) (hf0 : f 0 = 1) : f = Real.exp := by
  obtain ⟨C, hC⟩ := exists_smul_rexp hf
  have hzero := congrFun hC 0
  have hC_one : C = 1 := by simpa [hf0] using hzero.symm
  simpa [hC_one] using hC


end LeanSISSA.ExponentialODE
