/-
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Formalization

We model a bipartite finite-dimensional quantum system: Alice's degrees of freedom are
indexed by `A`, Bob's by `B`, and a joint state is a matrix `ρ : Matrix (A × B) (A × B) ℂ`
(no positivity or normalization is needed for the argument).

* `Frontier.ptraceAlice ρ` is the partial trace over Alice's system, i.e. the reduced
  state seen by Bob.
* A completely general local operation performed by Alice is a quantum channel given in
  Kraus form by operators `K i : Matrix A A ℂ` satisfying `∑ i, (K i)ᴴ * K i = 1`
  (trace preservation).  On the joint system it acts as `ρ ↦ ∑ i, (K i ⊗ 1) ρ (K i ⊗ 1)ᴴ`,
  see `Frontier.aliceChannel`.

`Frontier.no_communication` states that Bob's reduced state is completely unaffected by
any such local operation of Alice; in particular no information can be transmitted to Bob,
however entangled the state `ρ` is.
-/

namespace Frontier

open Matrix

variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I] [DecidableEq A] [DecidableEq B]

/-- The partial trace over Alice's subsystem: the reduced state seen by Bob. -/

noncomputable def ptraceAlice (ρ : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  Matrix.of fun b b' => ∑ a : A, ρ (a, b) (a, b')

/-- The operator `K ⊗ 1`: it acts as `K` on Alice's system and trivially on Bob's. -/
