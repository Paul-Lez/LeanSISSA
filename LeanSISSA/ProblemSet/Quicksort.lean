module

public import Mathlib.Data.List.Sort

/-! # Verifying a sorting algorithm

Prove that sort returns a sorted permutation of its input.
The termination proof is complete.
Useful declarations: `List.length_filter_le`, `List.mem_filter`, `List.Perm`,
`List.Perm.append`, `List.Perm.mem_iff`, `List.pairwise_append`, `List.pairwise_cons`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Sort.html
-/

public section

namespace LeanSISSA.Sort

open List

private theorem filter_attach_unattach (xs : List ℕ) (p : ℕ → Bool) :
    (xs.attach.filter (fun x => p x.1)).unattach = xs.filter p := by
  simp only [List.unattach_filter, List.unattach_attach]

/-- This function sorts a list of natural numbers. It uses the first element as the pivot.
It sorts the remaining elements below the pivot and the remaining elements at or above the pivot.
It puts the pivot between the two sorted lists. -/
def sort : List ℕ → List ℕ
  | [] => []
  | pivot :: xs =>
      sort (xs.filter (· < pivot)) ++ [pivot] ++ sort (xs.filter (pivot ≤ ·))
termination_by xs => xs.length
decreasing_by
  all_goals
    simp_wf
    simpa using (Nat.lt_succ_of_le (List.length_filter_le _ xs.attach))

/-- The output of sort is a permutation of the input.
Thus, it keeps the multiplicity of each element. -/
theorem quicksort_perm (xs : List ℕ) : (sort xs).Perm xs := by
  induction xs using sort.induct with
  | case1 => simp [sort]
  | case2 pivot xs ih₁ ih₂ =>
      simp only [sort]
      rw [filter_attach_unattach xs (fun x => decide (x < pivot))] at ih₁
      rw [filter_attach_unattach xs (fun x => decide (pivot ≤ x))] at ih₂
      calc
        _ ~ xs.filter (· < pivot) ++ [pivot] ++ xs.filter (pivot ≤ ·) :=
          (ih₁.append (List.Perm.refl [pivot])).append ih₂
        _ ~ pivot :: (xs.filter (· < pivot) ++ xs.filter (pivot ≤ ·)) := by
          simpa only [List.append_assoc, List.singleton_append, List.cons_append,
            List.nil_append] using
            (List.perm_append_comm (l₁ := xs.filter (· < pivot)) (l₂ := [pivot])).append_right
              (xs.filter (pivot ≤ ·))
        _ ~ pivot :: xs := List.Perm.cons pivot (by
          simpa only [← decide_not, not_lt] using
            List.filter_append_perm (fun x => decide (x < pivot)) xs)

/-- In the output of sort, each element is less than or equal to every subsequent element. -/
theorem quicksort_sorted (xs : List ℕ) : (sort xs).Pairwise (· ≤ ·) := by
  induction xs using sort.induct with
  | case1 => simp [sort]
  | case2 pivot xs ih₁ ih₂ =>
      simp only [sort]
      rw [filter_attach_unattach xs (fun x => decide (x < pivot))] at ih₁
      rw [filter_attach_unattach xs (fun x => decide (pivot ≤ x))] at ih₂
      have hlo (a : ℕ) (ha : a ∈ sort (xs.filter (· < pivot))) : a ≤ pivot := by
        have ha' := (quicksort_perm _).mem_iff.mp ha
        exact (of_decide_eq_true (List.mem_filter.mp ha').2).le
      have hhi (b : ℕ) (hb : b ∈ sort (xs.filter (pivot ≤ ·))) : pivot ≤ b := by
        have hb' := (quicksort_perm _).mem_iff.mp hb
        exact of_decide_eq_true (List.mem_filter.mp hb').2
      rw [List.pairwise_append, List.pairwise_append]
      refine ⟨⟨ih₁, by simp, ?_⟩, ih₂, ?_⟩
      · intro a ha b hb
        simpa only [List.mem_singleton.mp hb] using hlo a ha
      · intro a ha b hb
        rcases List.mem_append.mp ha with ha | ha
        · exact (hlo a ha).trans (hhi b hb)
        · simpa only [List.mem_singleton.mp ha] using hhi b hb

/-- The output of sort is a sorted permutation of the input. -/
theorem quicksort_correct (xs : List ℕ) :
    (sort xs).Perm xs ∧ (sort xs).Pairwise (· ≤ ·) := by
  exact ⟨quicksort_perm xs, quicksort_sorted xs⟩

end LeanSISSA.Sort
