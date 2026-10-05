import Mathlib
/-!
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open TensorProduct

/-- Complex conjugation acting on the complexification `ℂ ⊗[ℚ] V` of a rational vector
space `V` (conjugation on the left factor, identity on `V`).  It is only `ℚ`-linear
(it is conjugate-linear over `ℂ`). -/

theorem hodgeConjectureAt_zero (X : HodgeVariety H) : HodgeConjectureAt X 0 := by
  have h : hodgeClasses X 0 = ⊤ := by
    refine le_antisymm le_top fun v _ => ?_
    show (1 : ℂ) ⊗ₜ[ℚ] v ∈ (X.hs 0).piece 0 0
    rw [X.degree_zero_type]
    exact Submodule.mem_top
  rw [HodgeConjectureAt, h, X.alg_degree_zero]

/-- **The Hodge conjecture, stated, together with the Lean-checked reductions and base
cases that are proved here.**

For every smooth complex projective variety `X` (represented by its cohomological Hodge
data), the *Hodge conjecture* asserts

  `HodgeConjecture X : ∀ p, X.alg p = hodgeClasses X p`,

i.e. every rational cohomology class of type `(p,p)` is a rational linear combination of
classes of algebraic cycles.  The statement below records:

1. the always-valid inclusion: algebraic classes are Hodge classes;
2. the contrapositive reformulation in each codimension: the conjecture holds in
   codimension `p` iff no Hodge class fails to be algebraic;
3. the global reduction of the conjecture to the single inclusion
   `hodgeClasses X p ≤ X.alg p`;
4. the base case `p = 0`, which is proved unconditionally;
5. the vanishing case: whenever `H^{p,p} = 0`, the conjecture holds in codimension `p`. -/
