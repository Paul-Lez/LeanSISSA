module

public import Mathlib.Data.List.Sort

/-! # Verifying a sorting algorithm

Prove that this sorting algorithm returns a sorted permutation of its input.
The termination proof is complete.
Useful declarations: `List.length_filter_le`, `List.mem_filter`, `List.Perm`,
`List.Perm.append`, `List.Perm.mem_iff`, `List.pairwise_append`, `List.pairwise_cons`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Sort.html
-/

public section

namespace LeanSISSA.Sort

/-- This function sorts a list of natural numbers. It uses the first element as the pivot.
It sorts the remaining elements below the pivot and the remaining elements at or above the pivot.
It puts the pivot between the two sorted lists. -/
def sort : List ℕ → List ℕ
  | [] => []
  | pivot :: xs =>
      sort (xs.filter (· < pivot)) ++ [pivot] ++ sort (xs.filter (pivot ≤ ·))
-- The lines below are needed to prove that the function acutally terminates.
termination_by xs => xs.length
decreasing_by
  all_goals
    simp_wf
    simpa using (Nat.lt_succ_of_le (List.length_filter_le _ xs.attach))

/-- The output of quicksort is a permutation of the input. Thus, it keeps the multiplicity of
each element. -/
theorem quicksort_perm (xs : List ℕ) : (sort xs).Perm xs := by
  sorry

/-- In the output of quicksort, each element is less than or equal to every subsequent element. -/
theorem quicksort_sorted (xs : List ℕ) : (sort xs).Pairwise (· ≤ ·) := by
  sorry

/-- The output of quicksort is a sorted permutation of the input. -/
theorem quicksort_correct (xs : List ℕ) :
    (sort xs).Perm xs ∧ (sort xs).Pairwise (· ≤ ·) := by
  exact ⟨quicksort_perm xs, quicksort_sorted xs⟩

end LeanSISSA.Sort
