import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Kronecker
open scoped Matrix

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

/-!
# The no-communication theorem (finite-dimensional base case)

A bipartite quantum system with Alice's finite-dimensional factor indexed by `A` and Bob's
by `B` is modelled by density matrices `Matrix (A × B) (A × B) ℂ`; an arbitrary (possibly
entangled) joint state is such a matrix `rho`.

Alice performs an arbitrary local operation: a quantum channel acting on her factor only,
given in Kraus form by operators `K i : Matrix A A ℂ` with `∑ i, (K i)ᴴ * K i = 1`
(this includes unitaries, and also measurements whose outcome is discarded).  The
corresponding operation on the joint system is
`rho ↦ ∑ i, (K i ⊗ₖ 1) * rho * (K i ⊗ₖ 1)ᴴ`, i.e. it acts as the identity on Bob's factor.

The main theorem `Frontier.no_communication` states that Bob's reduced density matrix — the
partial trace over Alice's factor — is completely unaffected by such an operation.
Consequently (`Frontier.no_communication_prob`, `Frontier.no_communication_indistinguishable`)
the probability of every outcome of every measurement Bob can perform is unchanged, so no
information whatsoever is transmitted by Alice's choice of local operation.
-/

namespace Frontier

variable {A B ι κ : Type*} [Fintype A] [Fintype B] [Fintype ι] [Fintype κ]
  [DecidableEq A] [DecidableEq B]

/-- Bob's reduced density matrix: the partial trace of a bipartite operator over Alice's
factor `A`. -/

private theorem sum_comm₃ {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (g : α → β → γ → ℂ) :
    ∑ a, ∑ b, ∑ c, g a b c = ∑ b, ∑ c, ∑ a, g a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- **No-communication theorem** (finite-dimensional base case).

If Alice applies an arbitrary local quantum channel — Kraus operators `K i` on her factor,
satisfying the trace-preservation condition `∑ i, (K i)ᴴ * K i = 1`, tensored with the
identity on Bob's factor — to a joint (possibly entangled) state `rho`, then Bob's reduced
density matrix is unchanged. Hence Alice's local operations transmit no information to Bob. -/
