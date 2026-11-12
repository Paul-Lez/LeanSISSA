import Mathlib

/-! # A simple no-free-lunch theorem

This exercise gives the definitions and statements.
A deterministic learner uses labels from a fixed finite training set.
Useful declarations: `Finset.mem_insert`, `Function.update`, `Function.update_same`,
`Function.update_noteq`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Logic/Function/Basic.html
-/

namespace LeanSISSA.NoFreeLunch

/-- This condition says that the learner uses only the labels on `training`.
The learner gives the same prediction function for targets that agree on `training`.
The learner takes a full target function as input. The condition prevents access to other labels. -/
def UsesOnlyTraining {X : Type*} (training : Finset X)
    (learner : (X → Bool) → X → Bool) : Prop :=
  ∀ f g, (∀ x ∈ training, f x = g x) → learner f = learner g

/-- Assume that `z` is not in `training`. There is an alternative target with the same training labels.
For that target, the learner gives the wrong prediction at `z`.
The theorem gives a worst-case target. It does not give a probability distribution. -/
theorem unseen_point_failure {X : Type*} [DecidableEq X] (training : Finset X)
    (learner : (X → Bool) → X → Bool) (hlearner : UsesOnlyTraining training learner)
    (target : X → Bool) (z : X) (hz : z ∉ training) :
    ∃ alternative : X → Bool,
      (∀ x ∈ training, alternative x = target x) ∧
      learner alternative z ≠ alternative z := by
  sorry

end LeanSISSA.NoFreeLunch
