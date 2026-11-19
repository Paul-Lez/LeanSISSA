module

public import Mathlib

/-! # ReLU networks are piecewise linear

A one-hidden-layer ReLU network is locally affine away from finitely many activation roots.
Useful declarations: `Finset.sum`, `Set.Finite`, `max_eq_left`, `max_eq_right`.
Mathlib documentation: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Set/Finite/Basic.html
-/

public section
noncomputable section
open Filter Topology

namespace LeanSISSA.ReLUPiecewiseLinear

/-- This function gives a ReLU network with one input, one output, and one hidden layer.
The output is `c + ∑ i, a i * max 0 (w i * x + b i)`. -/
def network (n : ℕ) (a w b : Fin n → ℝ) (c x : ℝ) : ℝ :=
  c + ∑ i, a i * max 0 (w i * x + b i)

/-- This condition says that `f` is locally affine outside a finite set `S`.
For each `x ∉ S`, there is an open interval around `x` on which `f` is affine. -/
def piecewiseAffine (f : ℝ → ℝ) : Prop :=
  ∃ S : Finset ℝ, ∀ x ∉ S, ∃ l r m d : ℝ,
    l < x ∧ x < r ∧ ∀ y ∈ Set.Ioo l r, f y = m * y + d

/-- The network is locally affine outside a finite set. -/
theorem network_piecewiseAffine (n : ℕ) (a w b : Fin n → ℝ) (c : ℝ) :
    piecewiseAffine (network n a w b c) := by
  classical
  let roots : Finset ℝ := Finset.univ.image (fun i : Fin n => -b i / w i)
  refine ⟨roots, ?_⟩
  intro x hx
  have hlocal : ∀ i : Fin n, ∀ᶠ y in 𝓝 x,
      max 0 (w i * y + b i) = if 0 < w i * x + b i then w i * y + b i else 0 := by
    intro i
    by_cases hi : w i = 0
    · have hb : ∀ y : ℝ, max 0 (w i * y + b i) =
          if 0 < w i * x + b i then w i * y + b i else 0 := by
        intro y
        simp only [hi, zero_mul]
        split_ifs with h
        · exact max_eq_right h.le
        · exact max_eq_left (le_of_not_gt h)
      exact Filter.Eventually.of_forall hb
    · have harg : w i * x + b i ≠ 0 := by
        intro hz
        apply hx
        apply Finset.mem_image.mpr
        refine ⟨i, Finset.mem_univ _, ?_⟩
        field_simp [hi]
        linarith
      have hgcont : ContinuousAt (fun y : ℝ => w i * y + b i) x := by fun_prop
      rcases lt_or_gt_of_ne harg with hneg | hpos
      · have hevent := hgcont.eventually (isOpen_Iio.mem_nhds hneg)
        filter_upwards [hevent] with y hy
        have hy0 : w i * y + b i ≤ 0 := le_of_lt hy
        simp [not_lt_of_ge hneg.le, hy0]
      · have hevent := hgcont.eventually (isOpen_Ioi.mem_nhds hpos)
        filter_upwards [hevent] with y hy
        simp [hpos, le_of_lt hy]
  have hpieces : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
      max 0 (w i * y + b i) = if 0 < w i * x + b i then w i * y + b i else 0 := by
    rw [eventually_all]
    intro i
    exact hlocal i
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hpieces
  let m : ℝ := ∑ i, if 0 < w i * x + b i then a i * w i else 0
  let d : ℝ := c + ∑ i, if 0 < w i * x + b i then a i * b i else 0
  refine ⟨x - ε, x + ε, m, d, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · intro y hy
    rcases hy with ⟨hyL, hyR⟩
    have hyball : dist y x < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hybranches := hball hyball
    unfold network
    simp_rw [hybranches]
    dsimp [m, d]
    calc
      c + ∑ i, a i * (if 0 < w i * x + b i then w i * y + b i else 0) =
          c + ∑ i, ((if 0 < w i * x + b i then a i * w i else 0) * y +
            (if 0 < w i * x + b i then a i * b i else 0)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs <;> ring
      _ = (∑ i, if 0 < w i * x + b i then a i * w i else 0) * y +
          (c + ∑ i, if 0 < w i * x + b i then a i * b i else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        ring

/- Challenge:
- This holds for any number of hidden layers - generalise this!
- this result also holds in higher dimensions. Can you state and prove this?
-/


end LeanSISSA.ReLUPiecewiseLinear
