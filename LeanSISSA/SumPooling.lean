import Mathlib

/-! # Permutation-invariant sum pooling

This exercise gives the definitions and statements.
Useful declarations: `Equiv.sum_comp`, `Finset.sum_bij`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/Finset/Basic.html
-/
noncomputable section

namespace LeanSISSA.SumPooling

/-- This function applies the feature map `φ` to each input. It adds the resulting features.
It applies the output map `ρ` to the sum. -/
def pool {ι : Type*} [Fintype ι] (φ ρ : ℝ → ℝ) (x : ι → ℝ) : ℝ :=
  ρ (∑ i, φ (x i))

/-- A permutation of the inputs does not change the output of sum pooling. -/
theorem pool_permutation {ι : Type*} [Fintype ι] (φ ρ : ℝ → ℝ)
    (x : ι → ℝ) (σ : Equiv.Perm ι) :
    pool φ ρ (fun i => x (σ i)) = pool φ ρ x := by
  sorry

end LeanSISSA.SumPooling
