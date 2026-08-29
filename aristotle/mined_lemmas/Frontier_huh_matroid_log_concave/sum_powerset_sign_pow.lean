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

theorem sum_powerset_sign_pow {α : Type*} [DecidableEq α] (E : Finset α) :
    ∑ S ∈ E.powerset, (-1 : ℤ[X]) ^ S.card * X ^ (E.card - S.card) = (X - 1) ^ E.card := by
  have h := Finset.prod_add (fun _ : α => (-1 : ℤ[X])) (fun _ => X) E
  simp only [Finset.prod_const] at h
  rw [show ((-1 : ℤ[X]) + X) = X - 1 by ring] at h
  rw [h]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hS)]

/-- In the free matroid on `E`, every subset of `E` has rank equal to its cardinality. -/
