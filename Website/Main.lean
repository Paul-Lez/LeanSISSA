import VersoManual
import Mathlib

open Verso Genre Manual InlineLean

#docs (Manual) course "LeanSISSA" :=
:::::::

Welcome to the LeanSISSA reference. Use the menu to find resources, tactics, and commands.
The Lean examples use Mathlib. Select a tactic in an example to see the goal at that point.
A non-example shows a situation where the tactic fails. Hover over the marked code to see Lean’s error message.

# Resources
%%%
tag := "resources"
htmlSplit := .never
%%%

## Start learning

- [Lean installation instructions](https://lean-lang.org/install/): install Lean and its editor tools.
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/): a tutorial on formal mathematics.
- [LeanSISSA course repository](https://github.com/Paul-Lez/LeanSISSA): course files and exercises.
- [Git tutorial](https://leanprover-community.github.io/contribute/git.html): learn the Git commands used with Lean projects.

## Find definitions and get help

- [Mathlib](https://github.com/leanprover-community/mathlib4): the main Lean mathematics library. Browse its [documentation](https://leanprover-community.github.io/mathlib4_docs/).
- [Lean Zulip](https://leanprover.zulipchat.com/): ask questions and talk to the Lean community.
- [Loogle](https://loogle.lean-lang.org/): search for declarations by name or type.
- [Tactic list](https://leanprover-community.github.io/mathlib4_docs/tactics.html): find more tactics and their syntax.
- [Lean glossary](https://leanprover-community.github.io/glossary.html): look up terms used by the community.
- [Tau Ceti](https://github.com/TauCetiProject/TauCeti): an AI-built mathematics library.

## A few links

### Formal Verification in Action

- [AlphaProof and Signal](https://deepmind.google/blog/introducing-alphaproof-code/)
- [Anthropic and Theorem: formal verification](https://www.anthropic.com/research/formal-verification)
- [Harmonic and Tensordyne](https://www.harmonic.fun/aristotle/case-studies/tensordyne/)

### Tooling

- [Comparator](https://github.com/leanprover/comparator): check a proof against a statement and an axiom policy.
- [Palomar](https://palomar-registry.org/about): a registry for formal statements.

# Math keyboard shortcuts
%%%
tag := "keyboard-shortcuts"
htmlSplit := .never
%%%

In a Lean file in VS Code, type a backslash followed by an abbreviation.
For example, type `\forall` to enter `∀`. The Lean extension replaces a completed
abbreviation automatically. Press Tab to replace an abbreviation early, or move
the cursor away from it.

To see the full list, open the Lean command menu and choose **Documentation… →
Show Unicode Input Abbreviations**. These shortcuts use the Lean extension's
default settings.

## Logic and arrows

:::table +header
*
  * Symbol
  * Type
  * Meaning
*
  * `∀`
  * `\forall`
  * For every
*
  * `∃`
  * `\exists`
  * There exists
*
  * `¬`
  * `\not`
  * Not
*
  * `∧`
  * `\and`
  * And
*
  * `∨`
  * `\or`
  * Or
*
  * `→`
  * `\to`
  * Implies or function arrow
*
  * `←`
  * `\leftarrow`
  * Left arrow
*
  * `↔`
  * `\iff`
  * If and only if
*
  * `↦`
  * `\mapsto`
  * Maps to
:::

## Comparisons and sets

:::table +header
*
  * Symbol
  * Type
  * Meaning
*
  * `≤`
  * `\le`
  * Less than or equal to
*
  * `≥`
  * `\ge`
  * Greater than or equal to
*
  * `≠`
  * `\ne`
  * Not equal to
*
  * `∈`
  * `\in`
  * Is an element of
*
  * `∉`
  * `\notin`
  * Is not an element of
*
  * `⊆`
  * `\subseteq`
  * Is a subset of
*
  * `∪`
  * `\union`
  * Union
*
  * `∩`
  * `\inter`
  * Intersection
*
  * `∅`
  * `\emptyset`
  * Empty set
:::

## Numbers and operations

:::table +header
*
  * Symbol
  * Type
  * Meaning
*
  * `ℕ`
  * `\N`
  * Natural numbers
*
  * `ℤ`
  * `\Z`
  * Integers
*
  * `ℚ`
  * `\Q`
  * Rational numbers
*
  * `ℝ`
  * `\R`
  * Real numbers
*
  * `×`
  * `\times`
  * Multiplication or product type
*
  * `∑`
  * `\sum`
  * Sum
*
  * `∏`
  * `\prod`
  * Product
*
  * `∞`
  * `\infty`
  * Infinity
*
  * `√`
  * `\sqrt`
  * Square root
:::

## Letters and other symbols

:::table +header
*
  * Symbol
  * Type
  * Meaning
*
  * `α`
  * `\alpha`
  * Alpha
*
  * `β`
  * `\beta`
  * Beta
*
  * `γ`
  * `\gamma`
  * Gamma
*
  * `δ`
  * `\delta`
  * Delta
*
  * `ε`
  * `\epsilon`
  * Epsilon
*
  * `λ`
  * `\lambda`
  * Lambda
*
  * `⟨`
  * `\langle`
  * Left angle bracket
*
  * `⟩`
  * `\rangle`
  * Right angle bracket
*
  * `·`
  * `\cdot`
  * Bullet for a proof case
*
  * `₁`
  * `\_1`
  * Subscript 1
*
  * `₂`
  * `\_2`
  * Subscript 2
:::

# Tactic cheatsheet
%%%
tag := "tactics"
htmlSplit := .never
%%%

A tactic changes the current goal or proves it. Click a tactic in a code block to inspect the proof state.

## Elementary tactics
%%%
tag := "elementary-tactics"
%%%

### `rw`

`rw [h]` replaces the left side of an equality `h` with its right side in the goal. Use `rw [← h]` for the other direction, or `rw [h] at h₂` to change a hypothesis.

```lean
example (a b : Nat) (h : a = b) : a + 3 = b + 3 := by
  rw [h]

example (a b : Nat) (h : a = b) (hb : b = 7) : a = 7 := by
  rw [← h] at hb
  exact hb
```

Non-example:

```lean (error := true)
-- The goal has no occurrence of a to rewrite.
example (a b : Nat) (h : a = b) : b = b := by
  rw [h]
```

### `apply`

`apply h` works backwards from the conclusion of `h`. It creates goals for any inputs that Lean still needs.

```lean
example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp

example (a b : Nat) (h : a = b) : b = a := by
  apply Eq.symm
  exact h
```

Non-example:

```lean (error := true)
-- P is not the conclusion Q.
example (P Q : Prop) (hp : P) : Q := by
  apply hp
```

### `intro`

`intro x` moves an input or an assumption from the goal into the context and calls it `x`.

```lean
example : ∀ n : Nat, n = n := by
  intro n
  rfl

example (P Q : Prop) : P → Q → P := by
  intro hp hq
  exact hp
```

Non-example:

```lean (error := true)
-- An equality goal has no input to introduce.
example : 4 = 4 := by
  intro x
```

### `use`

`use x` gives `x` as a witness for an existential goal. Lean then asks for the remaining property of that witness.

```lean
example : ∃ n : Nat, n + 2 = 5 := by
  use 3

example (n : Nat) : ∃ m : Nat, m = n + 1 := by
  use n + 1
```

Non-example:

```lean (error := true)
-- This goal is an equality, not an existence claim.
example : 2 = 2 := by
  use 2
```

### `obtain`

`obtain ⟨x, hx⟩ := h` takes a witness `x` and its property `hx` from an existence claim. It can also split a conjunction into its two parts.

```lean
example (h : ∃ n : Nat, n = 6) : ∃ m : Nat, m + 1 = 7 := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [hn]

example (P Q : Prop) (h : P ∧ Q) : Q := by
  obtain ⟨hp, hq⟩ := h
  exact hq
```

Non-example:

```lean (error := true)
-- An arbitrary proposition does not contain an existential witness.
example (P : Prop) (h : P) : P := by
  obtain ⟨x, hx⟩ := h
```

## More advanced automation
%%%
tag := "automation-tactics"
%%%

### `induction'`

`induction' n with n ih` proves a statement about a natural number in a base case and a successor case. In the successor case, `ih` is the induction hypothesis.

```lean
example (n : Nat) : n + 0 = n := by
  induction' n with n ih
  · rfl
  · simp
```

Non-example:

```lean (error := true)
-- P is a proposition, not a natural number to split into cases.
example (P : Prop) (h : P) : P := by
  induction' P with x ih
```

### `simp`

`simp` rewrites expressions with a set of simplification rules. Give extra rules with `simp [h]` and simplify a hypothesis with `simp at h`.

```lean
example (n : Nat) : 0 + n = n := by
  simp

example (n : Nat) (h : n = 8) : n + 0 = 8 := by
  simp [h]
```

Non-example:

```lean (error := true)
-- Simplification alone does not prove an arbitrary proposition.
example (P : Prop) : P := by
  simp
```

### `norm_num`

`norm_num` proves many facts by calculating with numbers. It can also simplify numerical expressions in a hypothesis with `norm_num at h`.

```lean
example : (7 : Nat) * 8 = 56 := by
  norm_num

example : (3 : ℤ) < 11 := by
  norm_num
```

Non-example:

```lean (error := true)
-- Calculation alone cannot prove an arbitrary proposition.
example (P : Prop) : P := by
  norm_num
```

### `linarith`

`linarith` combines linear equalities and inequalities to prove a goal or find a contradiction. It works with types such as the integers and real numbers.

```lean
example (x : ℝ) (h : x ≤ 4) : x + 2 ≤ 6 := by
  linarith

example (x y : ℝ) (h : x + y = 10) (hx : x = 3) : y = 7 := by
  linarith
```

Non-example:

```lean (error := true)
-- There is no assumption that says x is zero.
example (x : ℝ) : x = 0 := by
  linarith
```

### `grind`

`grind` combines several automated proof methods. It can use the local assumptions and known facts to prove a goal.

```lean
example (a b c : Nat) (h : a = b) (k : b = c) : a = c := by
  grind

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  grind
```

Non-example:

```lean (error := true)
-- There is no assumption that establishes P.
example (P : Prop) : P := by
  grind
```

# Command cheatsheet
%%%
tag := "commands"
htmlSplit := .never
%%%

Commands define objects or ask Lean for information. They are written outside a tactic proof.

## `theorem`, `lemma`, and `example`

`theorem` and `lemma` give a name to a proof; they work the same way in Lean. `example` checks a proof without creating a name that you can use later.

```lean
theorem add_zero_demo (n : Nat) : n + 0 = n := by
  simp

lemma zero_add_demo (n : Nat) : 0 + n = n := by
  simp

example (n : Nat) : n = n := by
  rfl
```

## `variable`

`variable` declares inputs for later declarations. Lean includes a variable in a declaration when that declaration uses it.

```lean
section

variable (n : Nat)

theorem next_is_positive : 0 < n + 1 := by
  omega

end
```

## `section`

`section` starts a local scope, and `end` closes it. Variables and local settings inside the section stop being active after `end`.

```lean
section LocalInputs

variable (k : Nat)

example : k + 0 = k := by
  simp

end LocalInputs
```

## `namespace`

`namespace` adds a prefix to names declared inside it. Use `end` to close the namespace.

```lean
namespace CourseDemo

theorem self_eq (n : Nat) : n = n := by
  rfl

end CourseDemo

#check CourseDemo.self_eq
```

## `#check`

`#check` asks Lean for the type of an expression. It does not calculate the expression.

```lean
#check Nat.add_comm

#check (5 + 2 : Nat)
```

## `#eval`

`#eval` computes an expression and displays the result. The expression must be executable.

```lean
#eval (5 + 2 : Nat)

#eval [1, 2, 3].length
```

## `#synth`

`#synth` asks Lean to find an instance of a type class. For example, `Add Nat` gives the addition operation on natural numbers.

```lean
#synth Add Nat

#synth DecidableEq Nat
```

## `#where`

`#where` reports the current namespace and other active scope settings. It helps you see the context in which Lean reads a command.

```lean
namespace ScopeDemo

#where

end ScopeDemo
```

:::::::

def main (args : List String) : IO UInt32 :=
  manualMain course.toPart (options := args) (config := { htmlDepth := 1 })
