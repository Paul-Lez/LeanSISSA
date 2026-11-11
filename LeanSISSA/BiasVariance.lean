import Mathlib

/-! # Bias–variance decomposition

This exercise uses a finite uniform distribution of predictions for one fixed input.
The target is deterministic. Thus, the identity has no irreducible-noise term.
Useful declarations: `Finset.sum_sub_distrib`, `Finset.sum_mul`, `Finset.mul_sum`, `sq_nonneg`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Ring/Finset.html
-/

noncomputable section
namespace LeanSISSA.BiasVariance

/-- This function gives the arithmetic mean of `n` predictions. Each prediction has equal weight. -/
def mean (n : ℕ) (prediction : Fin n → ℝ) : ℝ :=
  (∑ i, prediction i) / n

/-- This function gives the mean of the squared differences between the predictions and their mean. -/
def variance (n : ℕ) (prediction : Fin n → ℝ) : ℝ :=
  (∑ i, (prediction i - mean n prediction) ^ 2) / n

/-- Let `n` be positive. The mean squared error is the variance plus the squared bias.
The bias is the difference between the mean prediction and the deterministic target. -/
theorem bias_variance (n : ℕ) (hn : 0 < n) (prediction : Fin n → ℝ) (target : ℝ) :
    (∑ i, (prediction i - target) ^ 2) / n =
      variance n prediction + (mean n prediction - target) ^ 2 := by
  sorry

end LeanSISSA.BiasVariance
