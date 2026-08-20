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

theorem hodgeConjecture_prod_iff (D₁ : HodgeDatum V p) (D₂ : HodgeDatum W p) :
    HodgeConjecture (D₁.prod D₂) ↔ HodgeConjecture D₁ ∧ HodgeConjecture D₂ := by
  show (D₁.alg.prod D₂.alg = (D₁.hs.prod D₂.hs).hodgeClasses p) ↔ _
  rw [HodgeStr.hodgeClasses_prod, Submodule.prod_eq_prod_iff]
  rfl

end Prod

/-!
## The statement
-/

/-- **Hodge statement.**

For a smooth complex projective variety `X` and `p : ℤ`, write `V = H^{2p}(X, ℚ)` with its
weight-`2p` rational Hodge structure, and let `alg ⊆ V` be the `ℚ`-span of the cycle classes of
the codimension-`p` algebraic subvarieties.  The **Hodge conjecture** asserts
`alg = Hdg^p := V ∩ H^{p,p}`, which is `Frontier.HodgeConjecture D` for the corresponding
`D : Frontier.HodgeDatum V p`.

This theorem records the formalised statement together with what is proved about it:

* the conjecture is equivalent to the single inclusion `Hdg^p ⊆ alg` (the reverse inclusion is
  part of the data, cycle classes being of type `(p,p)`);
* the base case in which there are no nonzero Hodge classes of type `(p,p)`;
* the base case of a Hodge structure concentrated in bidegree `(p,p)` all of whose classes are
  algebraic — for `p = 0` and `X` connected this is the classical degree-`0` case, where
  `H^0(X,ℚ) = ℚ·[X]` and the fundamental class `[X]` is algebraic;
* the reduction to summands: the conjecture for a direct sum of Hodge data is equivalent to the
  conjecture for each summand;
* nonvacuity: a datum satisfying all the axioms exists, and the conjecture holds for it. -/
