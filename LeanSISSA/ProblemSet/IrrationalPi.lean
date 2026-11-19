module

public import Mathlib

public section

open scoped Real

/-- `π` is irrational. -/
theorem irrational_π : Irrational π := by
  exact irrational_pi
