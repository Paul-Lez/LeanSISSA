import Mathlib

/-! # Finite-horizon Bellman equations

This exercise uses a deterministic system with two actions. Rewards and discount factors are real.
For an optimal-control interpretation, the discount factor must be nonnegative.
The recurrence and the action bound hold for any real discount factor.
Useful declarations: `le_max_left`, `le_max_right`, `max_le`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Basic.html
-/

noncomputable section
namespace LeanSISSA.Bellman

/-- This function gives the Bellman value for `n` decisions. The terminal reward is zero.
The system has deterministic transitions and two actions: `false` and `true`.
The immediate reward is `reward s a`. If `γ` is nonnegative, the value is optimal. -/
def value {S : Type*} (transition : S → Bool → S) (reward : S → Bool → ℝ) (γ : ℝ) :
    ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, s => max (reward s false + γ * value transition reward γ n (transition s false))
                    (reward s true + γ * value transition reward γ n (transition s true))

/-- For `n + 1` decisions, the value is the maximum of the two action values.
Each action value is the immediate reward plus `γ` times the value of the next state. -/
theorem bellman_equation {S : Type*} (transition : S → Bool → S) (reward : S → Bool → ℝ)
    (γ : ℝ) (n : ℕ) (s : S) :
    value transition reward γ (n + 1) s =
      max (reward s false + γ * value transition reward γ n (transition s false))
          (reward s true + γ * value transition reward γ n (transition s true)) := by
  sorry

/-- The value is at least the action value for each of the two actions. -/
theorem action_value_le {S : Type*} (transition : S → Bool → S) (reward : S → Bool → ℝ)
    (γ : ℝ) (n : ℕ) (s : S) (a : Bool) :
    reward s a + γ * value transition reward γ n (transition s a) ≤
      value transition reward γ (n + 1) s := by
  sorry

end LeanSISSA.Bellman
