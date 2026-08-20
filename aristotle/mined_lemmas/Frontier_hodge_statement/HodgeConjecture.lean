/-
# Hodge Statement
Category: Frontier — Moonshot
Target: Frontier.hodge_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## The set-up

Let `X` be a smooth complex projective variety and let `p : ℤ`.  The Hodge conjecture
concerns the rational cohomology group `V = H^{2p}(X, ℚ)`, which carries a rational
Hodge structure of weight `2p`: its complexification `ℂ ⊗[ℚ] V ≃ H^{2p}(X, ℂ)`
decomposes as an internal direct sum of the Hodge pieces `H^{i, 2p-i}`, and complex
conjugation on the complexification interchanges `H^{i, 2p-i}` and `H^{2p-i, i}`.

The group of *Hodge classes* is `Hdg^p(X) = V ∩ H^{p,p}`, the set of rational classes
whose image in the complexification lies in the middle piece.  The group of *algebraic
classes* is the ℚ-span of the cycle classes of the codimension-`p` algebraic subvarieties
of `X`; it is contained in `Hdg^p(X)`.

Since Mathlib contains neither the singular cohomology of a complex variety nor the cycle
class map, we axiomatise exactly this data: a `Frontier.HodgeDatum V p` records the
rational Hodge structure of weight `2p` on `V` together with the subspace of algebraic
classes and the (elementary) fact that algebraic classes are Hodge classes.  The Hodge
conjecture is then the statement `Frontier.HodgeConjecture`, namely that every Hodge class
is algebraic.
-/

section Complexification

variable (V : Type*) [AddCommGroup V] [Module ℚ V]

/-- Complex conjugation on the complexification `ℂ ⊗[ℚ] V` of a rational vector space `V`,
i.e. the map `z ⊗ v ↦ conj z ⊗ v`.  It is only `ℚ`-linear (it is conjugate-linear over `ℂ`). -/

def HodgeConjecture (D : HodgeDatum V p) : Prop :=
  D.alg = D.hs.hodgeClasses p

/-!
## Elementary reductions and base cases
-/

/-- Since algebraic classes are always Hodge classes, the Hodge conjecture reduces to the single
inclusion "every Hodge class is algebraic". -/
