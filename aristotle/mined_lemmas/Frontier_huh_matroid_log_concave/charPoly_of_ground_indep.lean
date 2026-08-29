/-
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
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

open Polynomial Finset

/-!
## Setting

Adiprasito–Huh–Katz proved that for any matroid `M` the absolute values of the
coefficients of the characteristic polynomial `χ_M` form a log-concave sequence
(the Rota–Heron–Welsh conjecture).

Here we formalise the *Whitney rank* definition of the characteristic polynomial,

`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`,

and prove the base case of the theorem: the Boolean matroid (the free matroid on a
finite ground set `E`), whose characteristic polynomial is `(X - 1)^{|E|}` and whose
Whitney numbers of the first kind are, up to sign, the binomial coefficients
`C(|E|, k)`.  Log-concavity of the coefficient sequence is therefore exactly
log-concavity of the binomial coefficients, which we prove from scratch.
-/

/-- A sequence of integers is *log-concave* when `c k * c (k+2) ≤ c (k+1)^2` for all `k`. -/

theorem charPoly_of_ground_indep {α : Type*} [DecidableEq α] {M : Matroid α} {E : Finset α}
    (hE : M.E = (E : Set α)) (hindep : M.Indep (E : Set α)) :
    charPoly M E = (X - 1) ^ E.card := by
  have : M = Matroid.freeOn (E : Set α) := Matroid.eq_freeOn_iff.2 ⟨hE, hindep⟩
  rw [this, charPoly_freeOn]

/-- The Whitney numbers of the first kind of a Boolean matroid are, in absolute value,
the binomial coefficients. -/
