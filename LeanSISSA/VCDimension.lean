import Mathlib

/-! # VC dimension and generalisation

This is an advanced open exercise. First, use the Mathlib definitions for set families.
Then use the Sauer–Shelah bound before you state the probability result.
Useful declarations: `Finset.Shatters`, `Finset.vcDim`, `Finset.card_le_card_shatterer`,
`Finset.card_shatterer_le_sum_vcDim`, `Real.exp_pos`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SetFamily/Shatter.html
-/

noncomputable section
namespace LeanSISSA.VCDimension

/-- This function gives the true classification error for a nonempty finite domain `X`.
The error is the fraction of points where the hypothesis and target disagree.
The distribution on `X` is uniform. -/
def trueError {X : Type*} [Fintype X] (hypothesis target : X → Bool) : ℝ := by
  sorry

/-- This function gives the empirical classification error for `n` sample positions, with `n > 0`.
The error is the fraction of positions where the hypothesis and target disagree.
Each sample position has a separate count, even if sample points are equal. -/
def empiricalError {X : Type*} (n : ℕ) (sample : Fin n → X)
    (hypothesis target : X → Bool) : ℝ := by
  sorry

/-- The Sauer–Shelah lemma gives an upper bound for the size of the set family `H`.
The bound depends on the VC dimension of `H` and the size of `X`. -/
theorem class_card_le {X : Type*} [Fintype X] [DecidableEq X]
    (H : Finset (Finset X)) :
    H.card ≤ ∑ k ∈ Finset.Iic H.vcDim, (Fintype.card X).choose k := by
  sorry

/-- This exercise gives a finite-domain VC uniform convergence bound.
Let `X` be a nonempty finite type. Let `H` be a finite family of subsets of `X`.
Assume that the VC dimension of `H` is at most `d`.
Let `target : X → Bool`. Let `n > 0` and `ε > 0`.
Each subset in `H` gives a Boolean classifier by its membership predicate.
Select `n` sample points independently from the uniform distribution on `X`.
For each classifier, take the absolute difference between `trueError` and `empiricalError`.
The probability that this difference is greater than `ε` for some classifier in `H` is at most:
`8 * (∑ k in Finset.range (d + 1), Nat.choose (2 * n) k) * Real.exp (-(n : ℝ) * ε^2 / 32)`.
Use a real number for the sum. Give a Lean statement for the probability and bound.
Replace `True` with the statement. Prove the statement.
First, you can prove the Sauer–Shelah bound for the number of labelings. -/
theorem uniform_convergence : True := by
  sorry

end LeanSISSA.VCDimension
