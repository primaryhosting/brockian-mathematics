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

/-!
# No-communication theorem (finite-dimensional Kraus form)

We model a bipartite quantum system with Alice's Hilbert space indexed by a finite
type `A` and Bob's by a finite type `B`, so that joint states are matrices indexed
by `A × B`.  A local operation performed by Alice is a quantum channel given by
Kraus operators `K i` acting on Alice's factor only, i.e. `K i ⊗ 1` on the joint
space, with `∑ i, (K i)ᴴ * (K i) = 1` (trace preservation).

The main result `Frontier.no_communication` says that Bob's reduced state
(the partial trace over Alice's subsystem) is completely unaffected by such an
operation, for *every* joint state `ρ` — in particular for entangled ones.
Consequently (`Frontier.no_communication_expectation`) the expectation value of
every observable measured by Bob alone is unchanged, so no information can be
transmitted.
-/

namespace Frontier

open scoped Matrix Kronecker

variable {A B ι : Type*} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq A] [DecidableEq B]

/-- The partial trace over Alice's subsystem: Bob's reduced density matrix. -/

noncomputable def ptraceA (ρ : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  Matrix.of fun b b' => ∑ a : A, ρ (a, b) (a, b')

/-- A local operation performed by Alice, in Kraus form: the Kraus operators act as
`K i ⊗ 1` on the joint system. -/
