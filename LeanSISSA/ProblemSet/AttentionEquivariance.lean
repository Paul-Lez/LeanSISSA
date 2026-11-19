module

public import Mathlib

/-! # Permutation equivariance of attention

Unscaled dot-product self-attention commutes with permutations of the token indices.
Use finite index types for tokens and features.
Useful declarations: `Equiv.sum_comp`,
`Real.exp_pos`, `Finset.sum_div`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/Finset/Basic.html
-/

public section
noncomputable section

namespace LeanSISSA.AttentionEquivariance

/-- This function gives the unscaled dot-product self-attention of `x`.
For token `i`, it calculates the score `∑ k, x i k * x j k` for each token `j`.
It applies softmax to the scores. It returns the weighted sum of the feature vectors. -/
noncomputable def attention {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → κ → ℝ) : ι → κ → ℝ := fun i k =>
  ∑ j, (Real.exp (∑ l, x i l * x j l) /
      ∑ j', Real.exp (∑ l, x i l * x j' l)) * x j k

/-- Let `σ` be a permutation of the token indices.
Apply attention to the input `fun i => x (σ i)`.
The output at `i` is the original output at `σ i`. -/
theorem attention_permutation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → κ → ℝ) (σ : Equiv.Perm ι) :
    attention (fun i => x (σ i)) = fun i => attention x (σ i) := by
  classical
  funext i k
  simp only [attention]
  let score (j : ι) := ∑ l, x (σ i) l * x j l
  have hden : (∑ j, Real.exp (score (σ j))) = ∑ j, Real.exp (score j) :=
    Equiv.sum_comp σ (fun j => Real.exp (score j))
  rw [hden]
  exact Equiv.sum_comp σ (fun j => (Real.exp (score j) / ∑ j', Real.exp (score j')) * x j k)

end LeanSISSA.AttentionEquivariance
