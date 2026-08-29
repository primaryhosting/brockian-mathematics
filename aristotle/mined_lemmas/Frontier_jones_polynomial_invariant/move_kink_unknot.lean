import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

We formalise Kauffman's state-sum model of the Kauffman bracket and the resulting
Jones polynomial, and prove that the writhe-normalised bracket is invariant under the
three Reidemeister moves.

A *link diagram* is recorded by the combinatorial data that the state sum needs: a finite
set `Fin m` of crossings, and, for every *state* `s : Fin m → Bool` (a choice of an `A`- or
`B`-smoothing at each crossing), the number `loops s` of closed curves in the completely
smoothed diagram.  The Kauffman bracket is then

`⟨D⟩ = ∑_s A^(#A-smoothings - #B-smoothings) · δ^(loops s - 1)`,  `δ = -A² - A⁻²`,

with values in the ring `ℤ[A, A⁻¹]` of Laurent polynomials.

The Reidemeister moves are encoded as relations between such data: each move is a purely
local modification of a diagram, and its effect on the state sum is exactly a statement
about how the loop counts of the diagrams before and after the move are related.  These
loop-count relations are the (planar, geometric) input to Kauffman's argument, and they
are what the constructors of `Frontier.Move` below record.
-/

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev Lau := LaurentPolynomial ℤ

/-- The monomial `A ^ n` inside `ℤ[A, A⁻¹]`. -/

lemma move_kink_unknot : Move kink 1 unknot 0 := by
  have h : Move ⟨0 + 1, kink.loops, kink.loops_pos⟩ (0 + 1)
      ⟨0, unknot.loops, unknot.loops_pos⟩ 0 := by
    refine Move.r1pos 0 unknot.loops unknot.loops_pos kink.loops kink.loops_pos ?_ ?_ <;>
      intro s <;> simp [kink, unknot]
  simpa using h

/-- The Kauffman bracket of the kinked unknot is `-A³`, but its Jones polynomial is that of
the unknot, namely `1`. -/
example : jones kink 1 = 1 := by
  rw [jones_polynomial_invariant move_kink_unknot, jones_unknot]

/-- The standard two-crossing diagram of the Hopf link: the two "equal" states have two
loops, the two "unequal" states have one. -/
