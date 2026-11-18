module

public import Mathlib

/-! # Entropy of a uniform random variable

This exercise uses Shannon entropy with the natural logarithm, so the unit is the nat.
A finite probability mass function gives the distribution of a random variable.
Useful declarations: `Real.log_inv`, `Finset.sum_const`, `Finset.card_univ`,
`Fintype.card_pos`, `Nat.cast_ne_zero`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Basic.html
-/

public section

noncomputable section
namespace LeanSISSA.UniformEntropy

/-- This function gives `-∑ i, p i * log (p i)` for a finite probability mass function `p`.
The natural logarithm gives entropy in nats. The definition also accepts other real functions. -/
def entropy {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -(∑ i, p i * Real.log (p i))

/-- This function gives the probability mass of each value in a finite nonempty uniform domain.
The same formula also defines a function when the type is empty. -/
def uniformMass {ι : Type*} [Fintype ι] (_i : ι) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹

/-- A uniform distribution on a nonempty finite type has entropy `log (card ι)` nats. -/
theorem entropy_uniform {ι : Type*} [Fintype ι] [Nonempty ι] :
    entropy (uniformMass : ι → ℝ) = Real.log (Fintype.card ι) := by
  sorry

/-- The uniform distribution on one point has zero entropy.
Hint: specialize `entropy_uniform` to `Fin 1` and simplify. -/
theorem entropy_uniform_one : entropy (uniformMass : Fin 1 → ℝ) = 0 := by
  sorry

/-- The uniform distribution on two points has entropy `log 2` nats.
Hint: specialize `entropy_uniform` to `Fin 2` and simplify. -/
theorem entropy_uniform_two : entropy (uniformMass : Fin 2 → ℝ) = Real.log 2 := by
  sorry

end LeanSISSA.UniformEntropy
