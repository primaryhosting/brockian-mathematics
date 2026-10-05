import Mathlib

/-!
# No Communication
Category: Frontier Physics
Target: Frontier.no_communication
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires all `import` commands to precede any other command,
including module doc comments, so `import Mathlib` appears on the first line and the
required header block follows immediately after it.

Statement formalized: local operations on one half of an entangled pair cannot transmit
information.  Concretely, for a bipartite system with Hilbert space `ℂ^A ⊗ ℂ^B`, any
quantum operation performed by Alice (a completely positive trace preserving map given in
Kraus form by operators `K i ⊗ 1`, with `∑ i, (K i)ᴴ * (K i) = 1`) leaves Bob's reduced
density matrix - the partial trace over Alice's factor - completely unchanged.  Hence no
measurement statistics available to Bob depend on Alice's choice of operation.
-/

namespace Frontier

open Matrix

variable {A B ι : Type*} [Fintype A] [Fintype B] [Fintype ι] [DecidableEq A] [DecidableEq B]

/-- Partial trace over the first (Alice) factor of a bipartite operator on `ℂ^A ⊗ ℂ^B`;
the result is an operator on Bob's factor `ℂ^B`. -/

noncomputable def ptraceFst (ρ : Matrix (A × B) (A × B) ℂ) : Matrix B B ℂ :=
  Matrix.of fun b b' => ∑ a : A, ρ (a, b) (a, b')

/-- The operator `K ⊗ 1`: `K` acts on Alice's factor, the identity acts on Bob's factor. -/
