module

public import Mathlib

/-! # Robustness of a linear classifier

A margin exceeding the norm bound for a perturbation preserves a positive classifier score.
Useful declarations: `Finset.abs_sum_le_sum_abs`, `Finset.sum_add_distrib`, `Real.sqrt_mul_self`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html
-/

public section
noncomputable section

namespace LeanSISSA.ClassifierRobustness

/-- This function gives the score `∑ i, w i * x i + b` of a linear classifier.
The feature vector has a finite number of real entries. -/
def score {ι : Type*} [Fintype ι] (w x : ι → ℝ) (b : ℝ) : ℝ :=
  (∑ i, w i * x i) + b

/-- This function gives the Euclidean norm `sqrt (∑ i, v i ^ 2)` of a finite real vector. -/
noncomputable def vectorNorm {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, v i ^ 2)

private theorem abs_sum_mul_le_norm {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    |∑ i, u i * v i| ≤ vectorNorm u * vectorNorm v := by
  calc
    |∑ i, u i * v i| ≤ ∑ i, |u i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |u i| * |v i| := by simp only [abs_mul]
    _ ≤ Real.sqrt (∑ i, |u i| ^ 2) * Real.sqrt (∑ i, |v i| ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ _ _
    _ = vectorNorm u * vectorNorm v := by simp only [sq_abs, vectorNorm]

/-- Assume that `score w x b` is positive and `vectorNorm w * vectorNorm δ < score w x b`.
Then the score at `fun i => x i + δ i` is positive.
The proof uses the Cauchy–Schwarz inequality. -/
theorem positive_under_perturbation {ι : Type*} [Fintype ι]
    (w x δ : ι → ℝ) (b : ℝ)
    (_hpos : 0 < score w x b)
    (hbound : vectorNorm w * vectorNorm δ < score w x b) :
    0 < score w (fun i => x i + δ i) b := by
  have hcs := abs_sum_mul_le_norm w δ
  have hpert : |∑ i, w i * δ i| < (∑ i, w i * x i) + b := by
    simpa [score] using hcs.trans_lt hbound
  change 0 < ∑ i, w i * (x i + δ i) + b
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have := abs_lt.mp hpert
  nlinarith

end LeanSISSA.ClassifierRobustness
