import LeanSISSA.ProblemSet.ReLULipschitz
import LeanSISSA.ProblemSet.ExponentialODE
import LeanSISSA.ProblemSet.SineODE
import LeanSISSA.ProblemSet.UniformEntropy
import LeanSISSA.ProblemSet.CauchyTheorem

/-! # Beginner exercises

Twelve short exercises rated ★ (one star) or ★★ (two stars).
Replace each `sorry` with a proof. The imported results are available to use.
The hints suggest useful declarations; finding their arguments is part of the exercise.
This student worksheet is intentionally separate from the completed library imports.
-/

namespace LeanSISSA.BeginnerExercises

open ReLULipschitz UniformEntropy CauchyTheorem

/-- ★: ReLU sends zero to zero. Hint: unfold `relu` and use `simp`. -/
theorem relu_zero : relu 0 = 0 := by
  sorry

/-- ★: ReLU sends nonpositive inputs to zero. Hint: `max_eq_left`. -/
theorem relu_of_nonpos (x : ℝ) (hx : x ≤ 0) : relu x = 0 := by
  sorry

/-- ★: ReLU is nonnegative. Hint: `le_max_left`. -/
theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := by
  sorry

/-- ★: Applying ReLU twice gives the same result. Hint: use nonnegativity. -/
theorem relu_idempotent (x : ℝ) : relu (relu x) = relu x := by
  sorry

/-- ★★: The initial value one determines the exponential solution.
Hint: use `ExponentialODE.exists_smul_rexp`, then evaluate the equality at zero
with `congrFun` to determine the constant. -/
theorem exponential_initial_one (f : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f x) x) (hf0 : f 0 = 1) : f = Real.exp := by
  sorry

/-- ★: The initial values one and zero determine the cosine solution.
Hint: `funext`, `SineODE.solution_eq`, and `simp`. -/
theorem cosine_initial_values (f g : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (g x) x) (hg : ∀ x, HasDerivAt g (-f x) x)
    (hf0 : f 0 = 1) (hg0 : g 0 = 0) : f = Real.cos := by
  sorry

/-- ★: The uniform distribution on one point has zero entropy.
Hint: specialize `entropy_uniform` to `Fin 1` and simplify. -/
theorem entropy_uniform_one : entropy (uniformMass : Fin 1 → ℝ) = 0 := by
  sorry

/-- ★: The uniform distribution on two points has entropy `log 2` nats.
Hint: specialize `entropy_uniform` to `Fin 2` and simplify. -/
theorem entropy_uniform_two : entropy (uniformMass : Fin 2 → ℝ) = Real.log 2 := by
  sorry

/-- ★: Expand the square of a sum. Hint: `ring`. -/
theorem square_add {R : Type*} [CommSemiring R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  sorry

/-- ★★: In a group, a product is one exactly when the second factor is the
inverse of the first. Hint: `mul_eq_one_iff_inv_eq` or cancellation. -/
theorem product_eq_one {G : Type*} [Group G] (g h : G) :
    g * h = 1 ↔ h = g⁻¹ := by
  sorry

/-- ★★: An element whose square is one equals its inverse.
Hint: rewrite `pow_two` and use the preceding exercise. -/
theorem inverse_eq_of_square_eq_one {G : Type*} [Group G] (g : G)
    (hg : g ^ 2 = 1) : g⁻¹ = g := by
  sorry

/-- ★★: A product-one tuple of length one has its sole entry equal to one.
Hint: inspect `x.property`, then simplify `List.ofFn`. -/
theorem product_one_single_entry {G : Type*} [Group G]
    (x : ProductOneTuples G 1) : x.val 0 = 1 := by
  sorry

end LeanSISSA.BeginnerExercises
