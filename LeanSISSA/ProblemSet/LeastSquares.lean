module

public import Mathlib

/-! # Least squares and orthogonality

At a global least-squares minimizer, each column is orthogonal to the residual.
Useful declarations: `Finset.sum_add_distrib`, `Finset.sum_mul`, `sq_nonneg`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Basic.html
-/

public section
noncomputable section

namespace LeanSISSA.LeastSquares

/-- This function gives the sum of squared residuals for a finite data matrix.
The sum is `∑ i, ((∑ j, X i j * w j) - y i)^2`. -/
def loss {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → κ → ℝ) (y : ι → ℝ) (w : κ → ℝ) : ℝ :=
  ∑ i, ((∑ j, X i j * w j) - y i) ^ 2

/-- Assume that `w` minimizes `loss X y` over all coefficient vectors.
Then the residual is orthogonal to every column of `X`.
For every `j`, the sum `∑ i, X i j * ((∑ k, X i k * w k) - y i)` is zero. -/
theorem residual_orthogonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → κ → ℝ) (y : ι → ℝ) (w : κ → ℝ)
    (hw : ∀ v, loss X y w ≤ loss X y v) :
    ∀ j, ∑ i, X i j * ((∑ k, X i k * w k) - y i) = 0 := by
  classical
  intro j
  let v : ℝ → κ → ℝ := fun t k => w k + if k = j then t else 0
  let g : ℝ → ℝ := fun t => loss X y (v t)
  have hmin : IsLocalMin g 0 := by
    refine Filter.Eventually.of_forall ?_
    intro t
    simpa [g, v] using hw (v t)
  have hderiv : HasDerivAt g
      (∑ i, 2 * (((∑ k, X i k * w k) - y i) * X i j)) 0 := by
    have hpred (i : ι) (t : ℝ) :
        (∑ k, X i k * v t k) = (∑ k, X i k * w k) + t * X i j := by
      simp [v, mul_add, mul_ite, Finset.sum_add_distrib, mul_comm]
    have hg : g = fun t => ∑ i,
        (((∑ k, X i k * w k) - y i) + t * X i j) ^ 2 := by
      funext t
      simp only [g, loss]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hpred]
      ring
    rw [hg]
    have hsumderiv := HasDerivAt.sum (u := Finset.univ)
        (A := fun i t => (((∑ k, X i k * w k) - y i) + t * X i j) ^ 2)
        (A' := fun i => 2 * (((∑ k, X i k * w k) - y i) * X i j))
        (fun i hi => by
          have hid := (hasDerivAt_id (0 : ℝ)).mul_const (X i j)
          have hinner := HasDerivAt.const_add ((∑ k, X i k * w k) - y i) hid
          convert hinner.pow 2 using 1
          · funext t
            simp [id]
          · norm_num
            ring)
    convert hsumderiv using 1
    · funext t
      simp
  have hzero := hmin.hasDerivAt_eq_zero hderiv
  have hsum : (∑ i, 2 * (((∑ k, X i k * w k) - y i) * X i j)) =
      2 * (∑ i, X i j * ((∑ k, X i k * w k) - y i)) := by
    rw [← Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)

end LeanSISSA.LeastSquares
