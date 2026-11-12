import Mathlib

/-! # Permutation equivariance of attention

This is an open exercise. Write the definitions and replace `True` with the stated property.
Use finite index types for tokens and features.
Useful declarations: `Equiv.sum_comp`,
`Real.exp_pos`, `Finset.sum_div`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/Finset/Basic.html
-/
noncomputable section

namespace LeanSISSA.AttentionEquivariance

/-- This function gives the unscaled dot-product self-attention of `x`.
For token `i`, it calculates the score `∑ k, x i k * x j k` for each token `j`.
It applies softmax to the scores. It returns the weighted sum of the feature vectors. -/
noncomputable def attention {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → κ → ℝ) : ι → κ → ℝ := by
  sorry

/-- Let `σ` be a permutation of the token indices.
Apply attention to the input `fun i => x (σ i)`.
For each `i`, the new output at `i` is equal to the original output at `σ i`.
Replace `True` with this statement. Prove the statement. -/
theorem attention_permutation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → κ → ℝ) (σ : Equiv.Perm ι) : sorry := by
  sorry

end LeanSISSA.AttentionEquivariance
