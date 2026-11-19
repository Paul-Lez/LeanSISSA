module

public import Mathlib

/-! # Fibonacci sum representations

The exercise asks for a finite set of indices whose Fibonacci values sum to `n`.
This is weaker than classical Zeckendorf's theorem, which also requires indices
at least two and no consecutive indices. We use Mathlib's canonical representation
to construct the witness, while preserving the exercise statement.
-/

public section

local instance : IsTrans ℕ (fun a b => b + 2 ≤ a) where
  trans _a _b _c hba hcb := hcb.trans (le_self_add.trans hba)

private theorem zeckendorf_nodup : ∀ l : List ℕ, List.IsZeckendorfRep l → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
      have h' := h
      simp only [List.IsZeckendorfRep, List.cons_append, List.isChain_iff_pairwise,
        List.pairwise_cons] at h'
      apply List.nodup_cons.mpr
      constructor
      · intro ha
        have hle := h'.1 a (by simp [ha])
        omega
      · have htail : List.IsZeckendorfRep l := by
          change List.IsChain _ (l ++ [0])
          exact (List.isChain_iff_pairwise).2 h'.2
        exact zeckendorf_nodup l htail

/-- Every positive integer can be written as a sum of distinct Fibonacci numbers. -/
theorem zeckendorf_existence (n : ℕ) (_hn : 0 < n) :
    ∃ s : Finset ℕ, s.sum Nat.fib = n := by
  let l := Nat.zeckendorf n
  refine ⟨l.toFinset, ?_⟩
  rw [List.sum_toFinset Nat.fib (zeckendorf_nodup l (Nat.isZeckendorfRep_zeckendorf n))]
  simp [l]


/- Mini challenge: one can also prove a uniqueness result on this (see https://en.wikipedia.org/wiki/Zeckendorf%27s_theorem).
State and prove this! -/
