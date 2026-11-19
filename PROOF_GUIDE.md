# Proof guide and difficulty ratings

This local `proofs` branch contains completed solutions for the current problem set
and introductory exercises. The original solutions have been migrated to the
`LeanSISSA/ProblemSet/` directory and Lean’s module system.
The twelve beginner exercises are also solved, in the topic modules under
`LeanSISSA/ProblemSet/`, following their redistribution on main. Their ratings
remain one or two stars.

The branch is based on main commit `fa85800` (19 November 2026).
Retired Bellman, bias–variance, no-free-lunch, and VC exercises are omitted, as
requested. The original working tree, including those proofs and the previous
README edits, is preserved in the local stash named
“Preserve local proofs and README before migration to current main”.

Ratings describe the work needed to discover a proof, including finding the right
Mathlib API. A short proof can still require a difficult idea. They are relative
to a beginner who has completed basic tactic exercises.

- ★☆☆☆☆: direct definitions, rewriting, or one familiar lemma.
- ★★☆☆☆: a short argument combining tactics and inequalities.
- ★★★☆☆: finite sums, case splits, reindexing, or a useful intermediate identity.
- ★★★★☆: substantial interaction between mathematical ideas and Lean APIs.
- ★★★★★: an advanced construction or a chain of substantial prerequisite results.

The table lists every original proof placeholder. Definition placeholders are
listed separately below. New helper lemmas support these tasks and are not
additional exercises.

| File | Original proving task | Difficulty | Main idea |
| --- | --- | --- | --- |
| `Softmax` | `softmax_pos` | ★★☆☆☆ | The exponential sum is positive, so the quotient is positive. |
| `Softmax` | `softmax_sum` | ★★☆☆☆ | Combine fractions and cancel the nonzero normalizer. |
| `Softmax` | `softmax_add_const` | ★★★☆☆ | Factor and cancel the common exponential. |
| `ReLULipschitz` | `relu_lipschitz` | ★★☆☆☆ | Apply the existing absolute-difference inequality for `max`. |
| `ReLULipschitz` | `lipschitz_comp` | ★★☆☆☆ | Chain the bounds, using nonnegativity when multiplying. |
| `GradientDescent` | `loss_step_le` | ★★☆☆☆ | Factor the updated error and bound its squared multiplier. |
| `GradientDescent` | `loss_step_lt` | ★★☆☆☆ | Use strict bounds and a positive squared error. |
| `SumPooling` | `pool_permutation` | ★★☆☆☆ | Reindex the sum with `Equiv.sum_comp`. |
| `AttentionEquivariance` | `attention_permutation` | ★★★★☆ | Reindex both the normalizer and the weighted feature sum. |
| `ClassifierRobustness` | `positive_under_perturbation` | ★★★☆☆ | Expand the perturbed score and apply Cauchy–Schwarz. |
| `OrdinaryLeastSquares` | `coefficient_minimises` | ★★★★☆ | Expand the loss as a quadratic and use the coefficient identity. |
| `OrdinaryLeastSquares` | `minimiser_unique` | ★★★★☆ | Compare to the proposed minimizer; the squared difference vanishes. |
| `Quicksort` | `quicksort_perm` | ★★★★☆ | Use recursive induction, append permutations, and the filter partition. |
| `Quicksort` | `quicksort_sorted` | ★★★★☆ | Combine recursively sorted lists using their pivot bounds. |
| `LeastSquares` | `residual_orthogonal` | ★★★★★ | Perturb one coordinate and differentiate the resulting loss at its minimum. |
| `ReLUPiecewiseLinear` | `network_piecewiseAffine` | ★★★★★ | Exclude finitely many roots and find a common neighborhood with fixed activation signs. |
| `UniversalApproximation` | `approximate` | ★★★★★ | Build polygonal interpolation from ReLU ramps and use uniform continuity. |

| File | Original definition task | Difficulty | What to encode |
| --- | --- | --- | --- |
| `AttentionEquivariance` | `attention` | ★★☆☆☆ | Nested dot-product sums, exponential normalization, and weighted features. |
| `ClassifierRobustness` | `score` | ★☆☆☆☆ | A finite dot product plus bias. |
| `ClassifierRobustness` | `vectorNorm` | ★☆☆☆☆ | The square root of the sum of squares. |
| `LeastSquares` | `loss` | ★☆☆☆☆ | A sum of squared residuals. |
| `ReLUPiecewiseLinear` | `network` | ★☆☆☆☆ | A finite weighted sum of ReLU activations plus bias. |
| `ReLUPiecewiseLinear` | `piecewiseAffine` | ★★☆☆☆ | A finite exceptional set and a local affine representation. |

## New upstream problems

No misformalisations were found in the new problems; their original statements
are preserved. The binomial proof uses induction and
Pascal's identity. The ODE proofs use uniqueness, including the prescribed
Lipschitz vector field for the sine system. Cauchy's theorem is proved through
tuple rotation and direct orbit–stabilizer counting; it does not invoke a
previous Cauchy or Sylow theorem.

| File | New proving task | Difficulty | Main idea |
| --- | --- | --- | --- |
| `BinomialTheorem` | `binomial_formula` | ★★★★☆ | Induct using Pascal's identity, split endpoints, and reindex the sums. |
| `ExponentialODE` | `eq_zero_of_hasDeriv_self_of_eval_zero` | ★★★☆☆ | Compare the solution with zero using ODE uniqueness. |
| `ExponentialODE` | `exists_smul_rexp` | ★★★☆☆ | Compare with the exponential solution having the same initial value. |
| `ExponentialODE` | `forall_hasDerivAt_eval_self_iff` | ★★☆☆☆ | Combine the characterization with the derivative of the exponential. |
| `ExponentialODE` | `deriv_eq_self_iff` | ★★★☆☆ | Translate between `deriv` and `HasDerivAt` using differentiability. |
| `SineODE` | `solution_eq` | ★★★★☆ | Prove the product vector field is Lipschitz and compare with an explicit solution. |
| `SineODE` | `eq_sin` | ★☆☆☆☆ | Substitute the initial values into the preceding formula. |
| `UniformEntropy` | `entropy_uniform` | ★★★☆☆ | Evaluate the constant sum and simplify the logarithm of an inverse. |
| `CauchyTheorem` | `card_product_one_tuples` | ★★★★☆ | The first entries determine the last through the inverse ordered product. |
| `CauchyTheorem` | `rotate_iterate` | ★★★☆☆ | Track the index shift under iteration and reduce modulo the tuple length. |
| `CauchyTheorem` | `rotation_action_one` | ★★★☆☆ | Relate the residue of one to one iteration, including length one. |
| `CauchyTheorem` | `rotate_fixed_iff` | ★★★★☆ | A fixed tuple has equal coordinates; its product is a power. |
| `CauchyTheorem` | `card_mod_fixed` | ★★★★★ | Partition into orbits; their sizes are one or the prime. |
| `CauchyTheorem` | `exists_element_order_prime` | ★★★★☆ | Divisibility forces a second fixed tuple, giving a nonidentity element of prime order. |

| File | New definition task | Difficulty | What to encode |
| --- | --- | --- | --- |
| `CauchyTheorem` | `rotate` | ★★★★☆ | Move the first entry to the end while preserving the noncommutative product-one condition. |
| `CauchyTheorem` | `rotationAction` | ★☆☆☆☆ | Define the action function by iteration. |
| `CauchyTheorem` | Rotation `AddAction` instance | ★★★★☆ | Use periodicity to prove the group action laws. |

## Beginner exercises now grouped by topic

| File | Task | Difficulty | Main idea |
| --- | --- | --- | --- |
| `ReLULipschitz` | `relu_zero` | ★☆☆☆☆ | Simplify the definition at zero. |
| `ReLULipschitz` | `relu_of_nonpos` | ★☆☆☆☆ | Use the maximum identity under the hypothesis. |
| `ReLULipschitz` | `relu_nonneg` | ★☆☆☆☆ | Zero is below the maximum. |
| `ReLULipschitz` | `relu_idempotent` | ★☆☆☆☆ | Apply nonnegativity to the outer maximum. |
| `ExponentialODE` | `exponential_initial_one` | ★★☆☆☆ | Evaluate the solution characterization at zero to find its coefficient. |
| `SineODE` | `cosine_initial_values` | ★☆☆☆☆ | Substitute initial values in the explicit solution. |
| `UniformEntropy` | `entropy_uniform_one` | ★☆☆☆☆ | Specialize the general result and simplify. |
| `UniformEntropy` | `entropy_uniform_two` | ★☆☆☆☆ | Specialize the general result and simplify. |
| `BinomialTheorem` | `square_add` | ★★☆☆☆ | Expand multiplication and rearrange sums, without `ring`. |
| `CauchyTheorem` | `product_eq_one` | ★★☆☆☆ | Use the inverse identity in each direction. |
| `CauchyTheorem` | `inverse_eq_of_square_eq_one` | ★★☆☆☆ | Rewrite the square and apply the preceding equivalence. |
| `CauchyTheorem` | `product_one_single_entry` | ★★☆☆☆ | Simplify the defining list product for length one. |

## Additional exercises from current main

| File | Task | Difficulty | Main idea |
| --- | --- | --- | --- |
| `KleinFour` | `a_mul_b` | ★☆☆☆☆ | Evaluate the multiplication table with `rfl`. |
| `KleinFour` | `e_mul` | ★☆☆☆☆ | Split into the four cases. |
| `KleinFour` | `mul_e` | ★☆☆☆☆ | Split into the four cases. |
| `KleinFour` | `mul_self` | ★☆☆☆☆ | Split into the four cases. |
| `KleinFour` | `mul_comm` | ★★☆☆☆ | Split into cases for both factors. |
| `KleinFour` | `mul_assoc` | ★★☆☆☆ | Split into cases for all three factors. |
| `KleinFour` | `inv_eq_self` | ★☆☆☆☆ | The inverse is defined as the identity function. |
| `KleinFour` | `square_eq_one` | ★☆☆☆☆ | Reduce the square to the earlier multiplication lemma. |
| `KleinFour` | `mul_mul_self` | ★★☆☆☆ | Reassociate, cancel the repeated factor, and simplify the identity. |
| `KleinFour` | `solve_mul` | ★★☆☆☆ | Substitute the equation and cancel the repeated factor. |
| `LiveSession` | `triangularNumber_succ` | ★★☆☆☆ | Split off the last term of the interval sum. |
| `LiveSession` | `triangularNumber_zero` | ★☆☆☆☆ | The interval is empty. |
| `LiveSession` | `exists_triangularNumber_eq` | ★☆☆☆☆ | Give the witness three and compute. |
| `LiveSession` | Positive triangular number divisible by three | ★☆☆☆☆ | Give the witness three and compute. |
| `LiveSession` | `infinitude_of_primes` | ★★★☆☆ | Choose a prime dividing `N! + 1` and exclude small divisors. |
| `LiveSession` | `brahmagupta_fibonacci` | ★★☆☆☆ | Normalize a polynomial identity with `ring`. |
| `LiveSession` | Group associativity example | ★☆☆☆☆ | Use the symmetry of `mul_assoc`. |
| `IrrationalPi` | `irrational_π` | ★☆☆☆☆ | Apply Mathlib’s irrationality theorem. |
| `Zeckendorf` | `zeckendorf_existence` | ★★★★☆ | Use the canonical representation, establish no duplicate indices, and convert its list sum to a finset sum. |

## Additional exercises on current main

Ratings for the irrationality exercises assume reuse of existing Mathlib theorems;
proving the mathematical results from first principles would be substantially harder.
The introductory files are under `LeanSISSA/GettingStarted/`; the other files are
under `LeanSISSA/ProblemSet/`.

| File | Task | Difficulty | Main idea |
| --- | --- | --- | --- |
| `MoreExercises` | key_identity | ★☆☆☆☆ | Normalize the cubic polynomial with `ring`. |
| `MoreExercises` | Set union membership | ★☆☆☆☆ | Simplify the membership definition. |
| `MoreExercises` | Symmetric difference membership | ★★☆☆☆ | Unfold membership and use propositional reasoning. |
| `MoreExercises` | Sum of 1, 2, 3 | ★☆☆☆☆ | Evaluate a concrete finite sum with `norm_num`. |
| `MoreExercises` | Twice the sum from 1 to n | ★★☆☆☆ | Induct, split off the endpoint, and use arithmetic. |
| `MoreExercises` | irrational_root_two | ★★☆☆☆ | Specialize the library theorem for prime square roots. |
| `MoreExercises` | irrational_root_prime | ★★☆☆☆ | Apply the prime-square-root irrationality theorem. |
| `TacticPractise` | Universal polynomial identity | ★☆☆☆☆ | Introduce the variable and use `ring`. |
| `TacticPractise` | exists_example | ★☆☆☆☆ | Choose two as the witness. |
| `TacticPractise` | dvd_square | ★★☆☆☆ | Extract a divisibility witness and construct a new one. |
| `TacticPractise` | square_dvd_square | ★★☆☆☆ | Square a divisibility witness. |
| `TacticPractise` | three_div_sq_add_two_mul | ★★★☆☆ | Induct using the cubic identity and divisibility witnesses. |
| `TacticPractise` | Sum of ones over Icc 1 n | ★★☆☆☆ | Count the interval entries. |
| `TacticPractise` | Rational quotient bounds | ★★☆☆☆ | Transfer natural bounds through casts and divide by a positive denominator. |
| `TacticPractise` | Exponential monotonicity | ★☆☆☆☆ | Cast the lower bound on the natural exponent. |
| `TacticPractise` | Translation of a strict inequality | ★☆☆☆☆ | Add the same constant to both sides. |
| `TacticPractise` | Monotonicity of squares | ★★☆☆☆ | Use nonnegativity to preserve a strict inequality. |
| `TacticPractise` | Product bounded by average squares | ★★☆☆☆ | Expand the nonnegative square of the difference. |
| `TacticPractise` | Chain of inequalities | ★☆☆☆☆ | Combine the hypotheses with `linarith`. |
| `TacticPractise` | primes_dvd | ★★★☆☆ | Split prime divisibility of a product and then a power. |
| `TacticPractise` | σ_pos | ★☆☆☆☆ | Add two positive quantities. |
| `TacticPractise` | sigmoid_continous | ★★★☆☆ | Compose continuous functions and show the denominator never vanishes. |
| `TacticPractise` | sigmoid_differentiable | ★★★☆☆ | Use `fun_prop` with positivity to discharge nonvanishing. |
| `TacticPractise` | sigmoid_derivative | ★★★★☆ | Differentiate the composition and inverse, then normalize the rational identity. |
| `LiveSession` | triangularNumber_succ | ★★☆☆☆ | Split the finite sum at its upper endpoint. |
| `LiveSession` | triangularNumber_zero | ★☆☆☆☆ | Simplify the empty sum. |
| `LiveSession` | exists_triangularNumber_eq | ★☆☆☆☆ | Choose three and evaluate. |
| `LiveSession` | Positive triangular multiple of three | ★☆☆☆☆ | Choose three and evaluate the inequalities and divisibility. |
| `LiveSession` | infinitude_of_primes | ★★★☆☆ | A prime divisor of N! + 1 cannot be at most N. |
| `LiveSession` | brahmagupta_fibonacci | ★★☆☆☆ | Normalize the sum-of-squares identity with `ring`. |
| `LiveSession` | Group associativity example | ★☆☆☆☆ | Apply associativity in the required direction. |
| `KleinFour` | a_mul_b | ★☆☆☆☆ | Compute the multiplication table with `rfl`. |
| `KleinFour` | e_mul | ★☆☆☆☆ | Split into four cases and compute. |
| `KleinFour` | mul_e | ★☆☆☆☆ | Split into four cases and compute. |
| `KleinFour` | mul_self | ★☆☆☆☆ | Split into four cases and compute. |
| `KleinFour` | mul_comm | ★★☆☆☆ | Split on both inputs and compute. |
| `KleinFour` | mul_assoc | ★★☆☆☆ | Split on all three inputs and compute. |
| `KleinFour` | inv_eq_self | ★☆☆☆☆ | Unfold the chosen inverse by definitional equality. |
| `KleinFour` | square_eq_one | ★☆☆☆☆ | Rewrite the square as the previously computed product. |
| `KleinFour` | mul_mul_self | ★★☆☆☆ | Associate, cancel the repeated element, and use the identity. |
| `KleinFour` | solve_mul | ★★☆☆☆ | Substitute the equation and cancel the repeated factor. |
| `IrrationalPi` | irrational_π | ★☆☆☆☆ | Reuse Mathlib’s irrationality theorem. |
| `Zeckendorf` | zeckendorf_existence | ★★★★☆ | Use the canonical representation, prove its indices are distinct, and convert a list sum to a finite-set sum. |

The five-star exercises are advanced extensions rather than introductory tactic
practice: local piecewise affine structure, least-squares orthogonality, universal
approximation, and orbit counting each require substantial prerequisites.

# Formalisation notes

Four retained original theorem statements concluded `True`, so they did not yet express
the mathematical properties in their docstrings:

- `attention_permutation` now states equality under token permutations.
- `network_piecewiseAffine` now asserts the defined local affine property.
- `residual_orthogonal` now assumes global loss minimization and states column orthogonality.
- `positive_under_perturbation` now has the documented margin hypotheses and positive-score conclusion.

These were open statement placeholders, rather than false mathematical theorems.
The completed statements follow their original docstrings. No counterexample to
an originally specified mathematical claim was found.

The ReLU network can have nonzero biases, so “piecewise affine” is the precise
term for the local conclusion (often called “piecewise linear” in ML).

The new `zeckendorf_existence` statement only asks for a finite set of indices
whose Fibonacci numbers sum to `n`. It omits the nonconsecutive-index condition
and restriction to indices at least two used in the classical uniqueness theorem.
The stated existence result is true; its signature is preserved. The optional
uniqueness mini-challenge remains a comment, rather than a theorem to fill in.

# Verification

- `lake build` succeeds for all current modules, including the live-session demos.
- A source scan excluding comments and strings finds no active `sorry`, `admit`,
  or custom `axiom` in the 23 Lean source files.
- All project declarations in the compiled environment were checked for
  transitive axiom dependencies: only `propext`, `Classical.choice`, and
  `Quot.sound` occur.
- Cauchy’s theorem and the binomial formula were checked transitively: neither
  uses a prohibited existing theorem.
- `git diff --check` passes. Some pre-existing proof-style linter warnings remain.

The root import file no longer imports the three exercises deleted on main;
this also repairs the missing-module imports inherited from that commit.
The original local README changes are preserved in the stash, and the branch
keeps main’s README unchanged.

The rebase to `fa85800` preserves main’s `LeanSISSA.Sort.sort` API, reordered
ReLU exercises, and separate rotation function/action instance. It also removes
an accidental extra `-/` in main’s binomial module so the file parses.
