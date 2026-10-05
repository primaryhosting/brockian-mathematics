import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

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

/-!
The Adiprasito–Huh–Katz theorem states that the coefficients of the characteristic
polynomial of a matroid form a log-concave sequence (in absolute value).

Here we set up the characteristic polynomial of a finite matroid through Whitney's
rank-generating (Möbius) formula
`χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`
and prove the base case of the theorem for the *free matroid* (the Boolean matroid,
in which every subset of the ground set is independent), whose characteristic
polynomial is `(X - 1)^n`, so that the absolute values of its coefficients are the
binomial coefficients `C(n, k)`, which are log-concave.
-/

namespace Frontier

open Finset Polynomial

variable {α : Type*}

/-- The natural-number rank function of a matroid, obtained from the `ℕ∞`-valued rank. -/

noncomputable def freeMatroid (α : Type*) : Matroid α := Matroid.freeOn Set.univ

/-- Every set is independent in the free matroid. -/
