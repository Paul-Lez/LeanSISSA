module

public import Mathlib

/-! # Universal approximation with ReLU

This exercise gives the definitions and statement. It is a difficult exercise.
First, examine simple piecewise-linear functions.
Useful declarations: `ContinuousOn`, `Set.Icc`, `Finset.sum`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousOn.html
-/

public section
noncomputable section

namespace LeanSISSA.UniversalApproximation

/-- This function gives a real-valued ReLU network with one hidden layer and `n` hidden neurons.
The input and output are real numbers. The output bias is `c`. -/
def network (n : ℕ) (a w b : Fin n → ℝ) (c x : ℝ) : ℝ :=
  c + ∑ i, a i * max 0 (w i * x + b i)

/-- A clipped ramp is zero before zero and one after one. -/
private def ramp (t : ℝ) : ℝ := max 0 t - max 0 (t - 1)

private lemma ramp_of_nonpos {t : ℝ} (ht : t ≤ 0) : ramp t = 0 := by
  simp [ramp, max_eq_left ht, max_eq_left (by linarith : t - 1 ≤ 0)]

private lemma ramp_of_one_le {t : ℝ} (ht : 1 ≤ t) : ramp t = 1 := by
  rw [ramp, max_eq_right (by linarith), max_eq_right (by linarith)]
  ring

private lemma ramp_of_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : ramp t = t := by
  simp [ramp, max_eq_right ht.1, max_eq_left (by linarith [ht.2] : t - 1 ≤ 0)]

/-- Accumulating clipped increments gives linear interpolation on each grid interval. -/
private lemma ramp_sum (v : ℕ → ℝ) (N j : ℕ) (hj : j < N) (t : ℝ)
    (hlo : (j : ℝ) ≤ t) (hhi : t ≤ j + 1) :
    v 0 + ∑ i ∈ Finset.range N, (v (i + 1) - v i) * ramp (t - i) =
      v j + (v (j + 1) - v j) * (t - j) := by
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_of_lt hj)]
  have htail : ∑ i ∈ Finset.Ico (j + 1) N,
      (v (i + 1) - v i) * ramp (t - i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : (j : ℝ) + 1 ≤ i := by exact_mod_cast (Finset.mem_Ico.mp hi).1
    rw [ramp_of_nonpos (by linarith), mul_zero]
  rw [htail, add_zero, Finset.sum_range_succ]
  have hbefore : ∑ i ∈ Finset.range j,
      (v (i + 1) - v i) * ramp (t - i) = v j - v 0 := by
    rw [← Finset.sum_range_sub v j]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Finset.mem_range.mp hi)
    rw [ramp_of_one_le (by linarith), mul_one]
  rw [hbefore, ramp_of_mem_Icc ⟨by linarith, by linarith⟩]
  ring

/-- Every finite sum of clipped ramps is a one-hidden-layer ReLU network. -/
private lemma ramps_are_network (v : ℕ → ℝ) (N : ℕ) (scale : ℝ) :
    ∃ (n : ℕ) (a w b : Fin n → ℝ) (c : ℝ), ∀ x,
      network n a w b c x =
        v 0 + ∑ i ∈ Finset.range N, (v (i + 1) - v i) * ramp (scale * x - i) := by
  let d : Fin N → ℝ := fun i => v (i + 1) - v i
  refine ⟨N + N, Fin.append d (fun i => -d i), fun _ => scale,
    Fin.append (fun i => -(i : ℝ)) (fun i => -((i : ℝ) + 1)), v 0, ?_⟩
  intro x
  simp only [network, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib, ← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp [d, ramp]
  ring_nf

/-- Let `f` be continuous on `[0, 1]` and let `ε` be positive.
There is a ReLU network with one hidden layer whose error is less than `ε`
at every point in `[0, 1]`. -/
theorem approximate (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (a w b : Fin n → ℝ) (c : ℝ),
      ∀ x ∈ Set.Icc (0 : ℝ) 1, |network n a w b c x - f x| < ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε / 2) (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  let N := m + 1
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hmesh : 1 / (N : ℝ) < δ := by simpa [N] using hm
  let v : ℕ → ℝ := fun i => f ((i : ℝ) / N)
  obtain ⟨n, a, w, b, c, hnet⟩ := ramps_are_network v N N
  refine ⟨n, a, w, b, c, ?_⟩
  intro x hx
  rw [hnet]
  by_cases hx1 : x = 1
  · subst x
    have hr : ∑ i ∈ Finset.range N, (v (i + 1) - v i) * ramp ((N : ℝ) * 1 - i) =
        v N - v 0 := by
      rw [← Finset.sum_range_sub v N]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hi
      rw [ramp_of_one_le (by linarith), mul_one]
    rw [hr]
    simp [v, ne_of_gt hN, hε]
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    let j := ⌊(N : ℝ) * x⌋₊
    have ht : 0 ≤ (N : ℝ) * x := mul_nonneg hN.le hx.1
    have hj : j < N := (Nat.floor_lt ht).mpr (by nlinarith)
    have hlo : (j : ℝ) ≤ (N : ℝ) * x := Nat.floor_le ht
    have hhi : (N : ℝ) * x ≤ (j : ℝ) + 1 := (Nat.lt_floor_add_one _).le
    rw [ramp_sum v N j hj _ hlo hhi]
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    have hp : (j : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hj0 hN.le, (div_le_one hN).mpr (by linarith)⟩
    have hq : ((j : ℝ) + 1) / N ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (by positivity) hN.le, (div_le_one hN).mpr hjN⟩
    have hpdist : dist ((j : ℝ) / N) x < δ := by
      rw [Real.dist_eq]
      apply lt_of_le_of_lt _ hmesh
      apply abs_le.mpr
      constructor <;> apply (mul_le_mul_iff_left₀ hN).mp <;>
        simp only [sub_mul, neg_mul, div_mul_cancel₀ _ (ne_of_gt hN)] <;> nlinarith
    have hqdist : dist (((j : ℝ) + 1) / N) x < δ := by
      rw [Real.dist_eq]
      apply lt_of_le_of_lt _ hmesh
      apply abs_le.mpr
      constructor <;> apply (mul_le_mul_iff_left₀ hN).mp <;>
        simp only [sub_mul, neg_mul, div_mul_cancel₀ _ (ne_of_gt hN)] <;> nlinarith
    have hpclose := hclose _ hp x hx hpdist
    have hqclose := hclose _ hq x hx hqdist
    rw [Real.dist_eq] at hpclose hqclose
    let θ : ℝ := (N : ℝ) * x - j
    have hθ0 : 0 ≤ θ := by dsimp [θ]; linarith
    have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
    have herr : v j + (v (j + 1) - v j) * ((N : ℝ) * x - j) - f x =
        (1 - θ) * (f ((j : ℝ) / N) - f x) +
          θ * (f (((j : ℝ) + 1) / N) - f x) := by
      simp only [v, Nat.cast_add, Nat.cast_one, θ]
      ring
    rw [herr]
    calc
      _ ≤ |(1 - θ) * (f ((j : ℝ) / N) - f x)| +
          |θ * (f (((j : ℝ) + 1) / N) - f x)| := abs_add_le _ _
      _ ≤ |f ((j : ℝ) / N) - f x| + |f (((j : ℝ) + 1) / N) - f x| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - θ), abs_of_nonneg hθ0]
        apply add_le_add
        · simpa using mul_le_mul_of_nonneg_right (by linarith : 1 - θ ≤ 1)
            (abs_nonneg (f ((j : ℝ) / N) - f x))
        · simpa using mul_le_mul_of_nonneg_right hθ1
            (abs_nonneg (f (((j : ℝ) + 1) / N) - f x))
      _ < ε := by linarith


end LeanSISSA.UniversalApproximation
